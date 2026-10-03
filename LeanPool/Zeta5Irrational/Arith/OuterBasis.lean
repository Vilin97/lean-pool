/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.ClassCount
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring.Basic

/-! # The outer-range basis

For `p = 2m + 1` and the tail poles `j ∈ (N, K]`, grouped by class `jc j` (`j ≡ ±c`):
row `(c, i)` (`i < Lo c`) is `tpol (rootsO c i)` with
`rootsO c i = {tail poles of other classes} + (i < nb c ? i·{c} : big c + (i - nb c)·{c})`,
where `big c` are the tail poles of class `c` above `p`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- The class of a natural number. -/
@[expose] def jc (hm : 2 * m + 1 = p) (j : ℕ) : Fin (m + 1) :=
  ccls hm (((j : ℤ) : ZMod p))

lemma sq_eq_iff_ccls (hm : 2 * m + 1 = p) (x y : ZMod p) :
    x ^ 2 = y ^ 2 ↔ ccls hm x = ccls hm y := by
  constructor
  · intro h
    have h2 : (x - y) * (x + y) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [sub_eq_zero.mp h3]
    · have : x = -y := by linear_combination h3
      rw [this]
      exact
        (ccls_unique hm (-y) (ccls hm y)
            (by
              rcases ccls_spec hm y with h4 | h4
              · right; rw [h4, neg_neg]
              · left; rw [h4])).symm
  · intro h
    have e : ∀ z : ZMod p, z ^ 2 = ((((ccls hm z : ℕ) : ℤ) : ZMod p)) ^ 2 := by
      intro z
      rcases ccls_spec hm z with h4 | h4 <;> rw [h4]; ring
    rw [e x, e y, h]

variable (hm : 2 * m + 1 = p) (n : ℕ)

/-- Tail poles `N < j ≤ K`. -/
@[expose] def tailO (n : ℕ) : Finset ℕ :=
  Icc (3 * n + 1) (40 * n)

/-- Outer pole indices belonging to the residue class `c`. -/
@[expose] def tailC (c : Fin (m + 1)) : Finset ℕ :=
  (tailO n).filter fun j => jc hm j = c

/-- Number of rows allocated to the outer residue class `c`. -/
@[expose] def LoC (c : Fin (m + 1)) : ℕ :=
  (tailC hm n c).card

/-- Outer pole indices in class `c` that exceed the prime `p`. -/
@[expose] def bigC (c : Fin (m + 1)) : Finset ℕ :=
  (tailC hm n c).filter fun j => p < j

/-- Number of outer poles in class `c` that exceed `p`. -/
@[expose] def nbC (c : Fin (m + 1)) : ℕ :=
  (bigC hm n c).card

/-- The roots of the outer row `(c, i)`. -/
@[expose] def rootsO (c : Fin (m + 1)) (i : ℕ) : Multiset ℤ :=
  ((tailO n).filter fun j => jc hm j ≠ c).val.map (fun j : ℕ => (j : ℤ)) +
    (if i < nbC hm n c then Multiset.replicate i ((c : ℕ) : ℤ)
    else
      (bigC hm n c).val.map (fun j : ℕ => (j : ℤ)) +
        Multiset.replicate (i - nbC hm n c) ((c : ℕ) : ℤ))

lemma sum_LoC : ∑ c, LoC hm n c = 37 * n := by
  have :=
    Finset.card_eq_sum_card_fiberwise (f := jc hm) (s := tailO n) (t := Finset.univ)
      (fun j _ => Finset.mem_univ _)
  unfold LoC tailC
  rw [← this, tailO, Nat.card_Icc]; omega

lemma card_rootsO (c : Fin (m + 1)) {i : ℕ} (hi : i < LoC hm n c) :
    (rootsO hm n c i).card < 37 * n := by
  unfold rootsO
  have hsplit := Finset.card_filter_add_card_filter_not (s := tailO n) (fun j => jc hm j = c)
  have htail : (tailO n).card = 37 * n := by rw [tailO, Nat.card_Icc]; omega
  have hnb : nbC hm n c ≤ LoC hm n c := Finset.card_filter_le _ _
  have hLo : LoC hm n c = ((tailO n).filter fun j => jc hm j = c).card := rfl
  have hother : ((tailO n).filter fun j => jc hm j ≠ c).card = 37 * n - LoC hm n c := by
    have :
      ((tailO n).filter fun j => jc hm j ≠ c).card =
        ((tailO n).filter fun a => ¬(jc hm a = c)).card :=
      rfl
    omega
  split_ifs with h
  · simp only [Multiset.card_add, Multiset.card_map, Finset.card_val, Multiset.card_replicate]
    omega
  · simp only [Multiset.card_add, Multiset.card_map, Finset.card_val, Multiset.card_replicate]
    have : nbC hm n c = (bigC hm n c).card := rfl
    omega

/-- The class of a class representative is itself. -/
lemma ccls_self (c : Fin (m + 1)) : ccls hm ((((c : ℕ) : ℤ) : ZMod p)) = c :=
  (ccls_unique hm _ c (Or.inl rfl)).symm

lemma sq_jc (j : ℕ) : (((j : ℤ) : ZMod p)) ^ 2 = ((((jc hm j : ℕ) : ℤ) : ZMod p)) ^ 2 := by
  rw [sq_eq_iff_ccls hm, ccls_self]; rfl

/-- `γ_c = -c²` in `𝔽_p`. -/
@[expose] def γO (c : Fin (m + 1)) : ZMod p :=
  -((((c : ℕ) : ℤ) : ZMod p)) ^ 2

lemma map_factor (γ : ℤ) :
    (X + C (γ ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p)) = X - C (-((γ : ZMod p)) ^ 2) := by
  simp [sub_eq_add_neg]

lemma prod_map_const_pow {s : Finset ℕ} {f : ℕ → (ZMod p)[X]} {q : (ZMod p)[X]}
    (h : ∀ j ∈ s, f j = q) : ∏ j ∈ s, f j = q ^ s.card := by
  rw [Finset.prod_congr rfl h, Finset.prod_const]

/-- **Reduction of the outer rows mod `p`.** -/
theorem rootsO_map_ZMod (c : Fin (m + 1)) (i : ℕ) :
    (tpolZ (rootsO hm n c i)).map (Int.castRingHom (ZMod p)) =
      (∏ c' ∈ Finset.univ.erase c, (X - C (γO (p := p) c')) ^ LoC hm n c') *
        (X - C (γO (p := p) c)) ^ i := by
  have hfac :
    ∀ j : ℕ,
      ((X + C (((j : ℤ)) ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p))) =
        X - C (γO (p := p) (jc hm j)) :=
    by intro j; rw [map_factor, γO]; congr 2; exact congrArg Neg.neg (sq_jc hm j)
  have hcc :
    ((X + C ((((c : ℕ) : ℤ)) ^ 2) : ℤ[X]).map (Int.castRingHom (ZMod p))) =
      X - C (γO (p := p) c) :=
    by rw [map_factor]; rfl
  unfold tpolZ rootsO
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_add, Multiset.prod_add]
  have h1 :
    ((((tailO n).filter fun j => jc hm j ≠ c).val.map (fun j : ℕ => (j : ℤ))).map
          ((Polynomial.map (Int.castRingHom (ZMod p))) ∘ fun γ : ℤ => X + C (γ ^ 2))).prod =
      ∏ c' ∈ Finset.univ.erase c, (X - C (γO (p := p) c')) ^ LoC hm n c' := by
    rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    simp only [Function.comp, hfac]
    rw [←
      Finset.prod_fiberwise_of_maps_to (g := jc hm) (t := Finset.univ.erase c)
        (fun j hj => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2, Finset.mem_univ _⟩)]
    refine Finset.prod_congr rfl fun c' hc' => ?_
    rw [prod_map_const_pow (q := X - C (γO (p := p) c'))
        (fun j hj => by rw [(Finset.mem_filter.mp hj).2])]
    congr 1
    unfold LoC tailC
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ (Finset.mem_erase.mp hc').1⟩, h3⟩
  rw [h1]
  congr 1
  split_ifs with h
  · rw [Multiset.map_replicate, Multiset.prod_replicate]; simp only [Function.comp, hcc]
  · rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_replicate,
      Multiset.prod_replicate, ← Finset.prod_eq_multiset_prod]
    simp only [Function.comp, hfac]
    rw [show jc hm ((c : ℕ)) = c from ccls_self hm c]
    rw [prod_map_const_pow (q := X - C (γO (p := p) c))
        (fun j hj => by rw [(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2]),
      ← pow_add]
    have : nbC hm n c = (bigC hm n c).card := rfl
    congr 1; omega

end Zeta5Irrational
