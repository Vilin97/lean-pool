/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.FibreCard

/-!
# Content-grouped counting identity

The identity
    ∑ f, (∏ j, (fibreCard f j)!) · ∏ i, x (f i) = n! · hVal x n
groups the sum over colourings `f : Fin n → Fin N` by content multiset
and uses an orbit-stabilizer argument.  The stabiliser count enters as
a hypothesis, discharged as `card_fixing_perms` in `StabCount.lean`.
-/

@[expose] public section

namespace RS

open Finset

variable {n N : ℕ}

/-! ### Basic helpers -/

/-- The weight of a colouring depends only on its content. -/
theorem prod_eq_content_prod (f : Fin n → Fin N) (x : Fin N → ℂ) :
    ∏ i : Fin n, x (f i) = ((content f).1.map x).prod := by
  change (Finset.univ.val.map (x ∘ f)).prod = ((Finset.univ.val.map f).map x).prod
  rw [Multiset.map_map]

/-- The fibre-factorial product equals the count-factorial product. -/
theorem fibreFactorial_eq_count_factorial (f : Fin n → Fin N) :
    ∏ j : Fin N, (fibreCard f j).factorial =
      ∏ j : Fin N, ((content f).1.count j).factorial :=
  Finset.prod_congr rfl fun j _ => by rw [fibreCard_eq_count]

/-- Mapping `univ.val` by a permutation gives `univ.val`. -/
private theorem perm_map_univ_val (σ : Equiv.Perm (Fin n)) :
    Finset.univ.val.map σ = Finset.univ.val := by
  have : Finset.univ.map σ.toEmbedding = Finset.univ :=
    Finset.map_univ_equiv σ
  exact_mod_cast congr_arg Finset.val this

/-- Precomposing by a permutation preserves content. -/
theorem content_comp_perm (f : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) :
    content (f ∘ σ) = content f := by
  unfold content; refine Subtype.ext ?_
  change Finset.univ.val.map (f ∘ ⇑σ) = Finset.univ.val.map f
  conv_lhs => rw [show (f ∘ ⇑σ) = f ∘ ⇑σ from rfl]
  rw [← Multiset.map_map f σ, perm_map_univ_val]

/-! ### Transitivity of the content-class action -/

/-- Two monotone tuples with the same content are equal. -/
private theorem monotone_eq_of_content_eq {h₁ h₂ : Fin n → Fin N}
    (hm₁ : Monotone h₁) (hm₂ : Monotone h₂)
    (hc : content h₁ = content h₂) : h₁ = h₂ := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedLE hm₁.sortedLE_ofFn hm₂.sortedLE_ofFn
  rw [← Multiset.coe_eq_coe]
  show (↑(List.ofFn h₁) : Multiset (Fin N)) = ↑(List.ofFn h₂)
  rw [← Fin.univ_val_map h₁, ← Fin.univ_val_map h₂]
  exact congrArg Subtype.val hc

/-- If two colourings have the same content, some permutation maps
one to the other. -/
theorem content_eq_exists_perm (f g : Fin n → Fin N)
    (h : content f = content g) :
    ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  have hsf := Tuple.monotone_sort f
  have hsg := Tuple.monotone_sort g
  have heq : f ∘ ⇑(Tuple.sort f) = g ∘ ⇑(Tuple.sort g) :=
    monotone_eq_of_content_eq hsf hsg
      ((content_comp_perm f _).trans (h.trans (content_comp_perm g _).symm))
  refine ⟨Tuple.sort f * (Tuple.sort g)⁻¹, funext fun i => ?_⟩
  change f ((Tuple.sort f) ((Tuple.sort g)⁻¹ i)) = g i
  have := congrFun heq ((Tuple.sort g).symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  exact this

/-! ### Existence of colourings with prescribed content -/

/-- Every `s : Sym (Fin N) n` is the content of some colouring. -/
theorem exists_content_eq (s : Sym (Fin N) n) :
    ∃ f : Fin n → Fin N, content f = s := by
  classical
  have hlen : s.1.toList.length = n := by
    rw [Multiset.length_toList]; exact s.2
  refine ⟨fun i => s.1.toList.get ⟨i.1, by omega⟩, Subtype.ext ?_⟩
  rw [show (content (fun i : Fin n => s.1.toList.get ⟨i.1, by omega⟩)).1 =
    Finset.univ.val.map (fun i : Fin n => s.1.toList.get ⟨i.1, by omega⟩)
    from rfl]
  rw [Fin.univ_val_map]
  rw [show (List.ofFn fun i : Fin n =>
      s.1.toList.get ⟨↑i, by omega⟩) = s.1.toList from by
    apply List.ext_get
    · simp
    · intro i hi₁ hi₂
      simp]
  exact Multiset.coe_toList s.1

/-! ### Coset counting -/

/-- The fibre of `σ ↦ f ∘ σ` over `g` bijects with the stabilizer
when `g` is in the orbit. -/
private theorem card_fibre_eq_stab (f g : Fin n → Fin N)
    (σ₀ : Equiv.Perm (Fin n)) (hσ₀ : f ∘ σ₀ = g) :
    (univ.filter (fun σ : Equiv.Perm (Fin n) => f ∘ σ = g)).card =
      (univ.filter (fun σ : Equiv.Perm (Fin n) => f ∘ σ = f)).card := by
  classical
  refine Finset.card_bij'
    (fun σ _ => σ * σ₀⁻¹) (fun τ _ => τ * σ₀) ?_ ?_ ?_ ?_
  · -- forward: f ∘ σ = g → f ∘ (σ * σ₀⁻¹) = f
    intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    ext i
    simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    have h1 : ∀ j, f (σ j) = g j := congrFun hσ
    have h2 : ∀ j, f (σ₀ j) = g j := congrFun hσ₀
    rw [h1, ← h2, Equiv.apply_symm_apply]
  · -- backward: f ∘ τ = f → f ∘ (τ * σ₀) = g
    intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    ext i
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    have h1 : ∀ j, f (τ j) = f j := congrFun hτ
    have h2 : ∀ j, f (σ₀ j) = g j := congrFun hσ₀
    rw [h1, h2]
  · intro σ _; simp [mul_assoc]
  · intro τ _; simp [mul_assoc]

/-- The fibre of `σ ↦ f ∘ σ` over `g` is empty when `g` is NOT
in the orbit. -/
private theorem card_fibre_eq_zero (f g : Fin n → Fin N)
    (h : ¬∃ σ : Equiv.Perm (Fin n), f ∘ σ = g) :
    (univ.filter (fun σ : Equiv.Perm (Fin n) => f ∘ σ = g)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun σ _ hfσ => h ⟨σ, hfσ⟩

/-! ### The orbit-stabilizer identity -/

/-- Orbit-stabilizer: class size times stabilizer size equals `n!`. -/
theorem orbit_stab (f₀ : Fin n → Fin N)
    (hstab₀ : (univ.filter (fun σ : Equiv.Perm (Fin n) => f₀ ∘ σ = f₀)).card =
      ∏ j : Fin N, (fibreCard f₀ j).factorial) :
    Fintype.card {g : Fin n → Fin N // content g = content f₀} *
      (∏ j : Fin N, ((content f₀).1.count j).factorial) = n.factorial := by
  classical
  have hperm : Fintype.card (Equiv.Perm (Fin n)) = n.factorial :=
    Fintype.card_perm.trans (by rw [Fintype.card_fin])
  -- Sum fiberwise: n! = ∑_g card{σ ∈ univ | f₀ ∘ σ = g}
  have hfib' : n.factorial =
      ∑ g : Fin n → Fin N,
        (univ.filter (fun σ : Equiv.Perm (Fin n) => f₀ ∘ σ = g)).card := by
    rw [← hperm]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  -- Each fibre depends on whether g is in the orbit
  have hfibre_val : ∀ g : Fin n → Fin N,
      (univ.filter (fun σ : Equiv.Perm (Fin n) => f₀ ∘ σ = g)).card =
      if content g = content f₀
      then (univ.filter (fun σ : Equiv.Perm (Fin n) => f₀ ∘ σ = f₀)).card
      else 0 := by
    intro g
    split
    case isTrue hc =>
      obtain ⟨σ₀, hσ₀⟩ := content_eq_exists_perm f₀ g hc.symm
      exact card_fibre_eq_stab f₀ g σ₀ hσ₀
    case isFalse hc =>
      apply card_fibre_eq_zero
      rintro ⟨σ, hσ⟩
      exact hc (show content g = content f₀ from hσ ▸ content_comp_perm f₀ σ)
  -- Simplify
  rw [Finset.sum_congr rfl (fun g _ => hfibre_val g)] at hfib'
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul] at hfib'
  rw [show (Finset.univ.filter (fun g : Fin n → Fin N =>
        content g = content f₀)).card =
      Fintype.card {g : Fin n → Fin N // content g = content f₀} from
    (Fintype.card_subtype _).symm] at hfib'
  rw [hstab₀, fibreFactorial_eq_count_factorial] at hfib'
  exact hfib'.symm

/-! ### Main theorem -/

/-- **The content-grouped count**: weighting each colouring by its
stabiliser size and its colour product sums to the factorial times
the complete homogeneous value. -/
theorem sum_fibreFactorial_weight' {n N : ℕ} (x : Fin N → ℂ)
    (hstab : ∀ f : Fin n → Fin N,
      (Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => f ∘ π = f)).card =
      ∏ j : Fin N, (fibreCard f j).factorial) :
    ∑ f : Fin n → Fin N,
        ((∏ j : Fin N, (fibreCard f j).factorial : ℕ) : ℂ) *
          ∏ i, x (f i) =
      (n.factorial : ℂ) * hVal x n := by
  classical
  -- Step 1: Group by content
  rw [show (∑ f : Fin n → Fin N,
        ((∏ j : Fin N, (fibreCard f j).factorial : ℕ) : ℂ) *
          ∏ i, x (f i)) =
      ∑ s : Sym (Fin N) n, ∑ f : {f // content f = s},
        ((∏ j : Fin N, (fibreCard f.1 j).factorial : ℕ) : ℂ) *
          ∏ i, x (f.1 i) from
    (Fintype.sum_fiberwise content _).symm]
  -- Step 2: Within each class, the summand is constant
  have hinner : ∀ s : Sym (Fin N) n,
      (∑ f : {f // content f = s},
        ((∏ j : Fin N, (fibreCard f.1 j).factorial : ℕ) : ℂ) *
          ∏ i, x (f.1 i)) =
      ↑(Fintype.card {f // content f = s}) *
        ((∏ j : Fin N, (s.1.count j).factorial : ℕ) : ℂ) *
        ((s.1.map x).prod) := by
    intro s
    have hsummand : ∀ (f : {f // content f = s}),
        ((∏ j : Fin N, (fibreCard f.1 j).factorial : ℕ) : ℂ) *
        ∏ i, x (f.1 i) =
      ((∏ j : Fin N, (s.1.count j).factorial : ℕ) : ℂ) *
        (s.1.map x).prod := by
      rintro ⟨f, hf⟩
      change ((∏ j : Fin N, (fibreCard f j).factorial : ℕ) : ℂ) *
        ∏ i, x (f i) = _
      rw [show (∏ j : Fin N, (fibreCard f j).factorial : ℕ) =
        (∏ j : Fin N, (s.1.count j).factorial : ℕ) from by
          rw [fibreFactorial_eq_count_factorial, hf]]
      rw [show (∏ i : Fin n, x (f i)) = (s.1.map x).prod from by
        rw [prod_eq_content_prod, hf]]
    simp_rw [hsummand]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  rw [Finset.sum_congr rfl (fun s _ => hinner s)]
  -- Step 3: Use orbit-stabilizer
  have horbstab : ∀ s : Sym (Fin N) n,
      ↑(Fintype.card {f // content f = s}) *
        ((∏ j : Fin N, (s.1.count j).factorial : ℕ) : ℂ) =
      (n.factorial : ℂ) := by
    intro s
    obtain ⟨f₀, hf₀⟩ := exists_content_eq s
    have h := orbit_stab f₀ (hstab f₀)
    rw [hf₀] at h
    exact_mod_cast h
  rw [Finset.sum_congr rfl (fun s _ => by rw [horbstab s])]
  -- Step 4: Factor out n!
  rw [← Finset.mul_sum, hVal]

end RS
