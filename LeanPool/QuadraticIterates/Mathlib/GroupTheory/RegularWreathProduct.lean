/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Homomorphisms from wreath products to abelian groups

`#(D ≀ᵣ Q →* A) = #(D →* A) · #(Q →* A)` for `A` abelian, and consequently the maximal
elementary abelian 2-quotient of the `n`-fold iterated wreath power of `C₂` has order `2 ^ n`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- For a finite commutative group `H` of exponent `2`, `#H = #(H →* C₂)` where
`C₂ = Multiplicative (ZMod 2)`. -/
theorem elem_ab_card_hom (H : Type*) [Group H] [Finite H]
    (hcomm : ∀ a b : H, a * b = b * a) (hexp : ∀ h : H, h ^ 2 = 1) :
    Nat.card H = Nat.card (H →* Multiplicative (ZMod 2)) := by
  let : CommGroup H := { ‹Group H› with mul_comm := hcomm }
  let : Module (ZMod 2) (Additive H) := AddCommGroup.zmodModule fun x ↦ by
    apply Additive.toMul.injective
    simpa [two_nsmul, pow_two] using hexp (Additive.toMul x)
  have hcardH : Nat.card H = 2 ^ Module.finrank (ZMod 2) (Additive H) := by
    rw [FiniteField.pow_finrank_eq_natCard 2 (Additive H)]
    exact Nat.card_congr (Additive.ofMul (α := H))
  have hcardHom : Nat.card (H →* Multiplicative (ZMod 2))
      = 2 ^ Module.finrank (ZMod 2) (Additive H) := by
    rw [Nat.card_congr ((MonoidHom.toAdditiveLeftMulEquiv (M := H) (N := ZMod 2)).toEquiv.trans
      (Multiplicative.toAdd (α := (Additive H →+ ZMod 2)))),
      Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2 (M := Additive H) (M₁ := ZMod 2)).toEquiv]
    simpa [Subspace.dual_finrank_eq, Nat.card_eq_fintype_card] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) (Additive H))
  rw [hcardH, hcardHom]

/-- In `D ≀ᵣ Q`, the base element `mk (mulSingle x d) 1` is the `inl x`-conjugate of `mk (mulSingle
1 d) 1`. -/
private theorem conj_base_single {D Q : Type} [Group D] [Group Q] [DecidableEq Q] (x : Q) (d : D) :
    RegularWreathProduct.mk (Pi.mulSingle x d) (1 : Q)
      = RegularWreathProduct.inl x * RegularWreathProduct.mk (Pi.mulSingle 1 d) 1
        * (RegularWreathProduct.inl x)⁻¹ := by
  apply RegularWreathProduct.ext
  · funext y
    simp only [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left,
      RegularWreathProduct.right_inl, RegularWreathProduct.left_inl,
      Pi.mul_apply, Pi.one_apply, one_mul, mul_one, inv_one]
    rcases eq_or_ne y x with hy | hy
    · subst y; simp
    · simp [hy, inv_mul_eq_one.not.mpr hy.symm]
  · simp [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right,
      RegularWreathProduct.right_inl]

/-- For `φ : (D ≀ᵣ Q) →* A` with `A` abelian, `φ (mk f 1)` is the product over coordinates of `φ` on
single-coordinate base elements. -/
private theorem base_prod_eq {D Q A : Type} [Group D] [Group Q] [CommGroup A] [Fintype Q]
    [DecidableEq Q] (φ : (D ≀ᵣ Q) →* A) (f : Q → D) :
    φ (RegularWreathProduct.mk f 1)
      = ∏ x, φ (RegularWreathProduct.mk (Pi.mulSingle x (f x)) (1 : Q)) := by
  have hbmul (g h : Q → D) :
      (RegularWreathProduct.mk g (1 : Q)) * (RegularWreathProduct.mk h 1)
        = RegularWreathProduct.mk (g * h) 1 := by
    apply RegularWreathProduct.ext
    · simp [RegularWreathProduct.mul_left]
    · simp [RegularWreathProduct.mul_def]
  have key (s : Finset Q) :
      φ (RegularWreathProduct.mk (fun y ↦ if y ∈ s then f y else 1) (1 : Q))
        = ∏ x ∈ s, φ (RegularWreathProduct.mk (Pi.mulSingle x (f x)) (1 : Q)) := by
    induction s using Finset.induction with
    | empty =>
        have hmk : RegularWreathProduct.mk
            (fun y : Q ↦ if y ∈ (∅ : Finset Q) then f y else 1) (1 : Q) = 1 := by
          apply RegularWreathProduct.ext
          · funext y; simp
          · simp [RegularWreathProduct.one_right]
        simpa [map_one] using congrArg φ hmk
    | insert a s ha ih =>
        have hsplit : (fun y ↦ if y ∈ insert a s then f y else 1)
            = Pi.mulSingle a (f a) * (fun y ↦ if y ∈ s then f y else 1) := by
          funext y
          by_cases hya : y = a
          · subst hya
            simp [Finset.mem_insert, Pi.mul_apply, Pi.mulSingle_eq_same, ha]
          · simp [Finset.mem_insert, hya, Pi.mul_apply]
        rw [hsplit, ← hbmul, map_mul, ih, Finset.prod_insert ha]
  simpa [Finset.mem_univ] using key Finset.univ

/-- The inclusion of the base group `D` into `D ≀ᵣ Q` at the identity coordinate. -/
private def baseHom {D Q : Type} [Group D] [Group Q] [DecidableEq Q] : D →* D ≀ᵣ Q where
  toFun d := RegularWreathProduct.mk (Pi.mulSingle 1 d) 1
  map_one' := by
    apply RegularWreathProduct.ext
    · simp [RegularWreathProduct.one_left]
    · simp [RegularWreathProduct.one_right]
  map_mul' d₁ d₂ := by
    apply RegularWreathProduct.ext
    · simp [RegularWreathProduct.mul_left, Pi.mulSingle_mul]
    · simp [RegularWreathProduct.mul_def]

private theorem baseHom_apply {D Q : Type} [Group D] [Group Q] [DecidableEq Q] (d : D) :
    (baseHom d : D ≀ᵣ Q) = RegularWreathProduct.mk (Pi.mulSingle 1 d) 1 := rfl

/-- Reconstruct a hom `(D ≀ᵣ Q) →* A` (with `A` abelian) from a hom on the base coordinate `D` and
one on `Q`. -/
private def reconHom {D Q A : Type} [Group D] [Group Q] [CommGroup A] [Fintype Q]
    (p : (D →* A) × (Q →* A)) : (D ≀ᵣ Q) →* A where
  toFun w := (∏ x, p.1 (w.left x)) * p.2 w.right
  map_one' := by simp
  map_mul' w₁ w₂ := by
    simp only [RegularWreathProduct.mul_def, Pi.mul_apply, map_mul]
    rw [Finset.prod_mul_distrib,
      show (∏ x, p.1 (w₂.left (w₁.right⁻¹ * x))) = ∏ x, p.1 (w₂.left x) from
        Equiv.prod_comp (Equiv.mulLeft w₁.right⁻¹) (fun x ↦ p.1 (w₂.left x))]
    simp [mul_assoc, mul_comm, mul_left_comm]

private theorem reconHom_apply {D Q A : Type} [Group D] [Group Q] [CommGroup A] [Fintype Q]
    (p : (D →* A) × (Q →* A)) (w : D ≀ᵣ Q) :
    reconHom p w = (∏ x, p.1 (w.left x)) * p.2 w.right := rfl

/-- Restricting a hom to the base coordinate and to `Q` is a bijection
`((D ≀ᵣ Q) →* A) ≃ (D →* A) × (Q →* A)` when `A` is abelian; `reconHom` is the inverse. -/
private def homEquivProd {D Q A : Type} [Group D] [Group Q] [CommGroup A] [Fintype Q]
    [DecidableEq Q] : ((D ≀ᵣ Q) →* A) ≃ (D →* A) × (Q →* A) where
  toFun φ := (φ.comp baseHom, φ.comp RegularWreathProduct.inl)
  invFun := reconHom
  left_inv φ := by
    have hconj (x : Q) (d : D) :
        φ (RegularWreathProduct.mk (Pi.mulSingle x d) (1 : Q)) = φ (baseHom d) := by
      rw [conj_base_single x d, map_mul, map_mul, baseHom_apply]; simp
    ext w
    simp only [reconHom_apply, MonoidHom.comp_apply]
    rw [Finset.prod_congr rfl (fun x _ ↦ (hconj x (w.left x)).symm),
      ← base_prod_eq φ w.left, ← map_mul]
    congr 1
    apply RegularWreathProduct.ext
    · rw [RegularWreathProduct.mul_left]; ext x; simp [RegularWreathProduct.left_inl]
    · simp [RegularWreathProduct.mul_def, RegularWreathProduct.right_inl,
        RegularWreathProduct.left_inl]
  right_inv p := by
    apply Prod.ext
    · ext d
      simp only [reconHom_apply, MonoidHom.comp_apply, baseHom_apply]
      rw [map_one, mul_one, Fintype.prod_eq_single (1 : Q)]
      · simp [Pi.mulSingle]
      · intro x hx
        rw [Pi.mulSingle_eq_of_ne hx, map_one]
    · ext q
      simp only [reconHom_apply, MonoidHom.comp_apply, RegularWreathProduct.left_inl,
        RegularWreathProduct.right_inl]
      simp [Fintype.prod_eq_single (1 : Q)]

/-- `#((D ≀ᵣ Q) →* A) = #(D →* A) · #(Q →* A)` for finite groups `D`, `Q` and finite abelian `A`. -/
theorem RegularWreathProduct.card_hom (D Q A : Type) [Group D] [Group Q] [CommGroup A]
    [Finite Q] :
    Nat.card ((D ≀ᵣ Q) →* A) = Nat.card (D →* A) * Nat.card (Q →* A) := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  rw [← Nat.card_prod]
  exact Nat.card_congr homEquivProd

/-- `#(C_2 →* C_2) = 2` for `C_2 = Multiplicative (ZMod 2)`. -/
private theorem card_hom_c2 :
    Nat.card (Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)) = 2 := by
  have hcases : ∀ a : Multiplicative (ZMod 2),
      a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 2) := by decide
  rw [Nat.card_eq_two_iff]
  refine ⟨1, MonoidHom.id _,
    fun h ↦ absurd (DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ZMod 2))) (by decide), ?_⟩
  ext φ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hcases (φ (Multiplicative.ofAdd (1 : ZMod 2))) with hg | hg
  · left; apply MonoidHom.ext; intro x; rcases hcases x with hx | hx <;> simp [hx, hg]
  · right; apply MonoidHom.ext; intro x; rcases hcases x with hx | hx <;> simp [hx, hg]

/-- `#([C_2]^n →* C_2) = 2^n`: the maximal elementary-abelian 2-quotient of `WreathPower n` has
`𝔽₂`-dimension `n`. -/
theorem wreath_max_elem_ab (n : ℕ) :
    Nat.card (IteratedWreathProduct (Multiplicative (ZMod 2)) n →* Multiplicative (ZMod 2))
      = 2 ^ n := by
  induction n with
  -- `IteratedWreathProduct _ 0` is `PUnit` by `rfl`; spelled out so instance search fires.
  | zero => exact Nat.card_unique (α := PUnit →* Multiplicative (ZMod 2))
  | succ n ih =>
      refine (RegularWreathProduct.card_hom (IteratedWreathProduct (Multiplicative (ZMod 2)) n)
        (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))).trans ?_
      rw [ih, card_hom_c2, pow_succ]
