/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CornerSquareDatum
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# The 𝒪-valued Čech complex of a rational covering, all degrees (T632)

[Wedhorn] Appendix A (l.5245–5270) verbatim, at the structure presheaf of a
`RationalCoveringData`: the group of `q`-cochains is the product of the
completed rational localizations at all `(q+1)`-tuple intersections
(`interList` of cover pieces, unnormalized — repetitions included), the
differential is the alternating sum of the face restrictions
`(dq f)_{i₀…i_{q+1}} = Σ (−1)^j f_{i₀…î_j…i_{q+1}}`, and the augmentation is
the product restriction from the base.

`IsCechAcyclicFull` is Definition A.1 verbatim: exactness of the augmented
complex `0 → 𝒪(X) → Č⁰ → Č¹ → ⋯` at every degree.
-/

@[expose] public section

@[expose] public section

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTateRing A]
  [DecidableEq A] [PlusSubring A] [HasLocLiftPowerBounded A]

variable (C : RationalCoveringData A) (hC : C.IsRational)

/-- The `(q+1)`-tuple intersection datum of cover pieces
([Wedhorn] `U_{i₀…i_q}`). -/
noncomputable def tupleDatum {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    RationalLocData A :=
  interList (fun i => (σ i).1) (fun i => hC.piece (σ i).2)

omit [HasLocLiftPowerBounded A] in
theorem tupleDatum_isRational {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    (tupleDatum C hC σ).IsRational :=
  interList_isRational _ _

omit [HasLocLiftPowerBounded A] in
theorem rationalOpen_tupleDatum {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s =
      ⋂ i, rationalOpen (σ i).1.T (σ i).1.s :=
  rationalOpen_interList _ _

omit [HasLocLiftPowerBounded A] in
/-- The tuple intersection is contained in each face's intersection. -/
theorem tupleDatum_subset_face {q : ℕ} (σ : Fin (q + 2) → ↥C.covers)
    (j : Fin (q + 2)) :
    rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s ⊆
      rationalOpen (tupleDatum C hC (σ ∘ j.succAbove)).T
        (tupleDatum C hC (σ ∘ j.succAbove)).s := by
  rw [rationalOpen_tupleDatum, rationalOpen_tupleDatum]
  exact Set.subset_iInter fun i => Set.iInter_subset _ (j.succAbove i)

omit [HasLocLiftPowerBounded A] in
/-- The tuple intersection is contained in the base. -/
theorem tupleDatum_subset_base {q : ℕ} (σ : Fin (q + 1) → ↥C.covers) :
    rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s ⊆
      rationalOpen C.base.T C.base.s := by
  rw [rationalOpen_tupleDatum]
  exact le_trans (Set.iInter_subset _ 0) (C.hsubset _ (σ 0).2)

/-- The group of unnormalized `q`-cochains with values in the structure
presheaf. -/
abbrev cechO (q : ℕ) : Type _ :=
  ∀ σ : Fin (q + 1) → ↥C.covers, presheafValue (tupleDatum C hC σ)

/-- The Čech differential ([Wedhorn] l.5262's `dq` formula). -/
noncomputable def cechD (q : ℕ) : cechO C hC q →+ cechO C hC (q + 1) where
  toFun f := fun σ => ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
    restrictionMapHom (tupleDatum C hC (σ ∘ j.succAbove)) (tupleDatum C hC σ)
      (tupleDatum_subset_face C hC σ j) (f (σ ∘ j.succAbove))
  map_zero' := by
    funext σ
    simp only [Pi.zero_apply, map_zero, smul_zero, Finset.sum_const_zero]
  map_add' f g := by
    funext σ
    show (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        restrictionMapHom _ _ (tupleDatum_subset_face C hC σ j)
          ((f + g) (σ ∘ j.succAbove))) = _
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The augmentation `𝒪(X) → Č⁰` ([Wedhorn] l.5273's `ε`). -/
noncomputable def cechAug : presheafValue C.base →+ cechO C hC 0 where
  toFun s := fun σ => restrictionMapHom C.base (tupleDatum C hC σ)
    (tupleDatum_subset_base C hC σ) s
  map_zero' := by
    funext σ
    simp only [map_zero, Pi.zero_apply]
  map_add' s t := by
    funext σ
    simp only [map_add, Pi.add_apply]

/-- **All-degree Čech acyclicity** ([Wedhorn] Definition A.1 verbatim):
the augmented unnormalized Čech complex
`0 → 𝒪(X) → Č⁰ → Č¹ → ⋯` is exact. -/
structure IsCechAcyclicFull : Prop where
  /-- Exactness at `𝒪(X)`: the augmentation is injective. -/
  aug_injective : Function.Injective (cechAug C hC)
  /-- Exactness at `Č⁰`: cocycles are restrictions of global sections. -/
  exact_zero : ∀ f : cechO C hC 0, cechD C hC 0 f = 0 →
    ∃ s : presheafValue C.base, cechAug C hC s = f
  /-- Exactness at `Č^{q+1}`: cocycles are coboundaries. -/
  exact_succ : ∀ (q : ℕ) (f : cechO C hC (q + 1)), cechD C hC (q + 1) f = 0 →
    ∃ g : cechO C hC q, cechD C hC q g = f

/-! ### The simplicial identities (mirroring `CechCohomology.lean`) -/

omit [HasLocLiftPowerBounded A] [DecidableEq A] in
private theorem face_face_lt' {q : ℕ} (j : Fin (q + 3)) (k : Fin (q + 2))
    (hjk : (k : ℕ) < j) (σ : Fin (q + 3) → ↥C.covers) (hj : j ≠ 0 := by omega) :
    (σ ∘ j.succAbove) ∘ k.succAbove =
      (σ ∘ (k.castSucc).succAbove) ∘ (j.pred hj).succAbove := by
  funext m
  simp only [Function.comp_apply]
  congr 1
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, apply_ite Fin.val, Fin.val_pred]
  split_ifs <;> omega

omit [HasLocLiftPowerBounded A] [DecidableEq A] in
private theorem face_face_ge' {q : ℕ} (j : Fin (q + 3)) (k : Fin (q + 2))
    (hjk : (j : ℕ) ≤ k) (σ : Fin (q + 3) → ↥C.covers)
    (hj : j.val < q + 2 := by omega) :
    (σ ∘ j.succAbove) ∘ k.succAbove =
      (σ ∘ (k.succ).succAbove) ∘ (⟨j.val, hj⟩ : Fin (q + 2)).succAbove := by
  funext m
  simp only [Function.comp_apply]
  congr 1
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, apply_ite Fin.val]
  split_ifs <;> omega

private theorem sign_zsmul_cancel' {G : Type*} [AddCommGroup G]
    (n m : ℕ) (x : G) : (-1 : ℤ) ^ n • ((-1 : ℤ) ^ m • x) +
    (-1 : ℤ) ^ (m + 1) • ((-1 : ℤ) ^ n • x) = 0 := by
  rw [← mul_zsmul, ← mul_zsmul, ← add_smul, pow_succ]
  ring_nf
  exact zero_smul _ _

/-- Transport of a doubly-restricted section across an equality of tuples
(proof-irrelevant in the subset witnesses). -/
private theorem res_res_eq_of_tuple_eq {q : ℕ} (f : cechO C hC q)
    {σ : Fin (q + 3) → ↥C.covers} {τ τ' : Fin (q + 1) → ↥C.covers}
    (hττ' : τ' = τ)
    (hmid : Fin (q + 2) → ↥C.covers) (hmid' : Fin (q + 2) → ↥C.covers)
    (h1 : rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s ⊆
      rationalOpen (tupleDatum C hC hmid').T (tupleDatum C hC hmid').s)
    (h2 : rationalOpen (tupleDatum C hC hmid').T (tupleDatum C hC hmid').s ⊆
      rationalOpen (tupleDatum C hC τ').T (tupleDatum C hC τ').s)
    (h1' : rationalOpen (tupleDatum C hC σ).T (tupleDatum C hC σ).s ⊆
      rationalOpen (tupleDatum C hC hmid).T (tupleDatum C hC hmid).s)
    (h2' : rationalOpen (tupleDatum C hC hmid).T (tupleDatum C hC hmid).s ⊆
      rationalOpen (tupleDatum C hC τ).T (tupleDatum C hC τ).s) :
    restrictionMapHom (tupleDatum C hC hmid') (tupleDatum C hC σ) h1
      (restrictionMapHom (tupleDatum C hC τ') (tupleDatum C hC hmid') h2
        (f τ')) =
    restrictionMapHom (tupleDatum C hC hmid) (tupleDatum C hC σ) h1'
      (restrictionMapHom (tupleDatum C hC τ) (tupleDatum C hC hmid) h2'
        (f τ)) := by
  subst hττ'
  have hc1 := congrFun (restrictionMap_comp (tupleDatum C hC τ')
    (tupleDatum C hC hmid') (tupleDatum C hC σ) h2 h1) (f τ')
  have hc2 := congrFun (restrictionMap_comp (tupleDatum C hC τ')
    (tupleDatum C hC hmid) (tupleDatum C hC σ) h2' h1') (f τ')
  simp only [Function.comp_apply] at hc1 hc2
  exact hc1.trans hc2.symm

/-- `d ∘ d = 0` for the 𝒪-valued Čech complex ([Wedhorn] Appendix A;
mirror of `cechDiff_comp_cechDiff`). -/
theorem cechD_comp_cechD (q : ℕ) (f : cechO C hC q) :
    cechD C hC (q + 1) (cechD C hC q f) = 0 := by
  funext σ
  show (∑ j : Fin (q + 3), (-1 : ℤ) ^ (j : ℕ) •
    restrictionMapHom _ _ (tupleDatum_subset_face C hC σ j)
      ((cechD C hC q f) (σ ∘ j.succAbove))) = 0
  have hexpand : ∀ j : Fin (q + 3),
      (cechD C hC q f) (σ ∘ j.succAbove) =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        restrictionMapHom (tupleDatum C hC ((σ ∘ j.succAbove) ∘ k.succAbove))
          (tupleDatum C hC (σ ∘ j.succAbove))
          (tupleDatum_subset_face C hC (σ ∘ j.succAbove) k)
          (f ((σ ∘ j.succAbove) ∘ k.succAbove)) := fun j => rfl
  simp only [hexpand, map_sum, map_zsmul, Finset.smul_sum]
  rw [← Finset.sum_product' Finset.univ Finset.univ]
  set T : Fin (q + 3) × Fin (q + 2) → presheafValue (tupleDatum C hC σ) :=
    fun p => (-1 : ℤ) ^ (p.1 : ℕ) • ((-1 : ℤ) ^ (p.2 : ℕ) •
      restrictionMapHom _ _ (tupleDatum_subset_face C hC σ p.1)
        (restrictionMapHom _ _
          (tupleDatum_subset_face C hC (σ ∘ p.1.succAbove) p.2)
          (f ((σ ∘ p.1.succAbove) ∘ p.2.succAbove)))) with hT
  change ∑ p ∈ Finset.univ ×ˢ Finset.univ, T p = 0
  let inv : Fin (q + 3) × Fin (q + 2) → Fin (q + 3) × Fin (q + 2) := fun p =>
    if _ : (p.2 : ℕ) < (p.1 : ℕ) then
      (⟨p.2.val, by omega⟩, ⟨p.1.val - 1, by have := p.1.isLt; omega⟩)
    else
      (⟨p.2.val + 1, by have := p.2.isLt; omega⟩, ⟨p.1.val, by
        have := p.2.isLt; omega⟩)
  apply Finset.sum_involution (fun p _ => inv p)
  · rintro ⟨j, k⟩ _
    dsimp only [inv]
    split_ifs with h
    · simp only [hT]
      have hj_ne : j ≠ 0 := by
        intro hj0
        simp only [hj0, Fin.val_zero] at h
        omega
      have hface := face_face_lt' C j k h σ hj_ne
      have heq : (σ ∘ (⟨k.val, by omega⟩ : Fin (q + 3)).succAbove) ∘
          (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin (q + 2)).succAbove =
          (σ ∘ j.succAbove) ∘ k.succAbove := by
        rw [show (⟨k.val, by omega⟩ : Fin (q + 3)) = k.castSucc from
            Fin.ext (by simp only [Fin.val_castSucc]),
          show (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin (q + 2)) =
            j.pred hj_ne from Fin.ext (by simp only [Fin.val_pred])]
        exact hface.symm
      rw [res_res_eq_of_tuple_eq C hC f heq _ _
        (tupleDatum_subset_face C hC σ ⟨k.val, by omega⟩)
        (tupleDatum_subset_face C hC
          (σ ∘ (⟨k.val, by omega⟩ : Fin (q + 3)).succAbove)
          ⟨j.val - 1, by have := j.isLt; omega⟩)
        (tupleDatum_subset_face C hC σ j)
        (tupleDatum_subset_face C hC (σ ∘ j.succAbove) k)]
      rw [← mul_zsmul, ← mul_zsmul, ← add_smul]
      have hsign : (-1 : ℤ) ^ (j : ℕ) =
          (-1 : ℤ) ^ ((j : ℕ) - 1) * (-1) := by
        conv_lhs =>
          rw [show (j : ℕ) = (j : ℕ) - 1 + 1 from by omega, pow_succ]
      rw [hsign]
      ring_nf
    · push Not at h
      simp only [hT]
      have hface := face_face_ge' C j k h σ (by have := k.isLt; omega)
      have heq : (σ ∘ (⟨k.val + 1, by have := k.isLt; omega⟩ :
          Fin (q + 3)).succAbove) ∘
          (⟨j.val, by have := k.isLt; omega⟩ : Fin (q + 2)).succAbove =
          (σ ∘ j.succAbove) ∘ k.succAbove := by
        rw [show (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (q + 3)) =
            k.succ from Fin.ext (by simp only [Fin.val_succ])]
        exact hface.symm
      rw [res_res_eq_of_tuple_eq C hC f heq _ _
        (tupleDatum_subset_face C hC σ ⟨k.val + 1, by have := k.isLt; omega⟩)
        (tupleDatum_subset_face C hC
          (σ ∘ (⟨k.val + 1, by have := k.isLt; omega⟩ :
            Fin (q + 3)).succAbove)
          ⟨j.val, by have := k.isLt; omega⟩)
        (tupleDatum_subset_face C hC σ j)
        (tupleDatum_subset_face C hC (σ ∘ j.succAbove) k)]
      exact sign_zsmul_cancel' (j : ℕ) (k : ℕ) _
  · rintro ⟨j, k⟩ _ _
    dsimp only [inv]
    split_ifs with h
    · intro heq
      have h1 := congr_arg Prod.fst heq
      simp only [Fin.ext_iff] at h1
      omega
    · intro heq
      have h1 := congr_arg Prod.fst heq
      simp only [Fin.ext_iff] at h1
      omega
  · rintro ⟨j, k⟩ _
    dsimp only [inv]
    split_ifs <;>
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  · rintro ⟨j, k⟩ _
    dsimp only [inv]
    by_cases h1 : (k : ℕ) < (j : ℕ)
    · simp only [h1, dif_pos, Fin.val_mk]
      rw [dif_neg (by omega)]
      exact Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext rfl)
    · push Not at h1
      have h2 : ¬ (k : ℕ) < (j : ℕ) := by omega
      rw [dif_neg h2, dif_pos (show (j : ℕ) < (k : ℕ) + 1 by omega)]
      exact Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp))

/-- `d⁰ ∘ ε = 0`: the two face restrictions of an augmented section agree. -/
theorem cechD_comp_cechAug (s : presheafValue C.base) :
    cechD C hC 0 (cechAug C hC s) = 0 := by
  funext σ
  show (∑ j : Fin 2, (-1 : ℤ) ^ (j : ℕ) •
    restrictionMapHom _ _ (tupleDatum_subset_face C hC σ j)
      (restrictionMapHom C.base _
        (tupleDatum_subset_base C hC (σ ∘ j.succAbove)) s)) = 0
  rw [Fin.sum_univ_two]
  have h0 := congrFun (restrictionMap_comp C.base
    (tupleDatum C hC (σ ∘ (0 : Fin 2).succAbove)) (tupleDatum C hC σ)
    (tupleDatum_subset_base C hC _) (tupleDatum_subset_face C hC σ 0)) s
  have h1 := congrFun (restrictionMap_comp C.base
    (tupleDatum C hC (σ ∘ (1 : Fin 2).succAbove)) (tupleDatum C hC σ)
    (tupleDatum_subset_base C hC _) (tupleDatum_subset_face C hC σ 1)) s
  simp only [Function.comp_apply] at h0 h1
  show (-1 : ℤ) ^ ((0 : Fin 2) : ℕ) • restrictionMap _ _
      (tupleDatum_subset_face C hC σ 0)
      (restrictionMap C.base _ (tupleDatum_subset_base C hC _) s) +
    (-1 : ℤ) ^ ((1 : Fin 2) : ℕ) • restrictionMap _ _
      (tupleDatum_subset_face C hC σ 1)
      (restrictionMap C.base _ (tupleDatum_subset_base C hC _) s) = 0
  rw [h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  exact add_neg_cancel _

end ValuationSpectrum
