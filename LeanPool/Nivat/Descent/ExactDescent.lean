/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.LowComplexity
public import LeanPool.Nivat.Algebra.LineErosion
public import LeanPool.Nivat.Descent.FiberBudget
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Pattern complexity under a Laurent operator

Section 2 of `paper/nivat.tex`.

* `multiplierMap_injective` completes the dimension calculation in Lemma 2.1.
* `localFilter_transpose` identifies the transpose with Laurent multiplication.
* `translatedSpan_eq_ker` proves equation `eq:full-kernel`.
* `exact_complexity_descent` is Theorem 2.2 (`thm:descent`).
* `exists_smaller_low_complexity_rectangle` is Corollary 2.3 (`cor:line-descent`).

The geometry of supported multiples is in `Nivat.Algebra.RectangleSupport`;
the finite fiber-counting argument is in `Nivat.Descent.FiberBudget`.
-/

public section

namespace Nivat.Descent

open Nivat.Algebra

/-- The space `V_R(d)` spanned by all translated restrictions of `d`.
Defined in the proof of Theorem 2.2 (`thm:descent`). -/
noncomputable def translatedSpan (d : Configuration ℚ) (R : Finset Lattice) :
    Submodule ℚ (R → ℚ) := Submodule.span ℚ (patterns d R)

/-- The forward-shift coefficient pairing is evaluation of the Laurent action.
This is the pairing computation in Theorem 2.2 (`thm:descent`). -/
private theorem dotProduct_patternAt (R : Finset Lattice) (b : R → ℚ)
    (c : Configuration ℚ) (u : Lattice) :
    dotProductEquiv ℚ R b (patternAt c R u) = act (windowPolynomial R b) c u := by
  classical
  rw [act_windowPolynomial]
  change (∑ z : R, b z * c (z.1 + u)) = ∑ z : R, b z * c (u + z.1)
  simp only [add_comm u]


/-- A coefficient vector annihilates `V_R(d)` exactly when its polynomial annihilates `d`.
This is the perpendicular-space identification in Theorem 2.2 (`thm:descent`). -/
theorem dotProduct_mem_dualAnnihilator_iff (d : Configuration ℚ) (R : Finset Lattice)
    (b : R → ℚ) :
    dotProductEquiv ℚ R b ∈ (translatedSpan d R).dualAnnihilator ↔
      act (windowPolynomial R b) d = 0 := by
  classical
  constructor
  · intro hb
    funext u
    have h := (Submodule.mem_dualAnnihilator _).mp hb (patternAt d R u)
      (Submodule.subset_span ⟨u, rfl⟩)
    rw [act_windowPolynomial]
    change (∑ z : R, b z * d (u + z.1)) = 0
    change (∑ z : R, b z * d (z.1 + u)) = 0 at h
    simpa only [add_comm u] using h
  · intro hann
    apply (Submodule.mem_dualAnnihilator _).mpr
    have hle : translatedSpan d R ≤ LinearMap.ker (dotProductEquiv ℚ R b) := by
      apply Submodule.span_le.mpr
      rintro p ⟨u, rfl⟩
      have h := congrFun hann u
      rw [act_windowPolynomial] at h
      change (∑ z : R, b z * d (z.1 + u)) = 0
      simpa only [add_comm u, Pi.zero_apply] using h
    intro p hp
    exact hle hp

/-- Restrict Laurent coefficients to a finite window.
This implements the identification with `ℚ^R` at the start of Section 2. -/
def coefficientRestriction (R : Finset Lattice) : Laurent →ₗ[ℚ] (R → ℚ) where
  toFun f z := f.coeff z.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `Φ` on polynomials supported in `S`, with coefficients read on `R`.
This is the map `Φ : ℚ^S → ℚ^R` in Lemma 2.1 (`lem:supported`). -/
@[expose] noncomputable def multiplierMap (Φ : Laurent) (R S : Finset Lattice) :
    (S → ℚ) →ₗ[ℚ] (R → ℚ) :=
  (coefficientRestriction R).comp ((LinearMap.mulLeft ℚ Φ).comp (windowPolynomialLinear S))

/-- The coefficient formula for multiplication in Lemma 2.1 (`lem:supported`). -/
theorem multiplierMap_apply (Φ : Laurent) (R S : Finset Lattice) (b : S → ℚ) (z : R) :
    multiplierMap Φ R S b z = (Φ * windowPolynomial S b).coeff z.1 := rfl

/-- Support containment makes coefficient restriction lossless.
This is the identification of supported multiples in Lemma 2.1 (`lem:supported`). -/
private theorem multiplierMap_reconstruct (Φ : Laurent) (R S : Finset Lattice)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S)
    (b : S → ℚ) : windowPolynomial R (multiplierMap Φ R S b) = Φ * windowPolynomial S b :=
  windowPolynomial_reconstruct R _ ((hfit _).mpr (windowPolynomial_support S b))

/-- Multiplication by a nonzero Laurent polynomial is injective.
This gives the dimension `|S|` in Lemma 2.1 (`lem:supported`). -/
theorem multiplierMap_injective (Φ : Laurent) (hΦ : Φ ≠ 0) (R S : Finset Lattice)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S) :
    Function.Injective (multiplierMap Φ R S) := by
  intro a b hab
  apply windowPolynomial_injective S
  apply mul_left_cancel₀ hΦ
  simpa only [multiplierMap_reconstruct Φ R S hfit] using
    congrArg (windowPolynomial R) hab

/-- The perpendicular space of `V_R(d)` is the image of multiplication by `Φ`.
This is the chain of equalities preceding `eq:full-kernel` in Theorem 2.2. -/
theorem dualAnnihilator_eq_multiplier_range (d : Configuration ℚ) (Φ : Laurent)
    (R S : Finset Lattice)
    (hexact : ∀ f : Laurent, act f d = 0 ↔ Φ ∣ f)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S) :
    (translatedSpan d R).dualAnnihilator =
      LinearMap.range ((dotProductEquiv ℚ R).toLinearMap.comp (multiplierMap Φ R S)) := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    let b := (dotProductEquiv ℚ R).symm ℓ
    have hb : dotProductEquiv ℚ R b = ℓ := (dotProductEquiv ℚ R).apply_symm_apply ℓ
    have hann : act (windowPolynomial R b) d = 0 :=
      (dotProduct_mem_dualAnnihilator_iff d R b).mp (hb.symm ▸ hℓ)
    obtain ⟨g, hg⟩ := (hexact _).mp hann
    have hgs : g.coeff.support ⊆ S := (hfit g).mp (by
      rw [← hg]
      exact windowPolynomial_support R b)
    refine ⟨fun z : S => g.coeff z.1, ?_⟩
    change dotProductEquiv ℚ R (multiplierMap Φ R S (fun z => g.coeff z.1)) = ℓ
    rw [← hb]
    congr 1
    apply windowPolynomial_injective R
    rw [multiplierMap_reconstruct Φ R S hfit, windowPolynomial_reconstruct S g hgs, ← hg]
  · rintro ⟨b, rfl⟩
    apply (dotProduct_mem_dualAnnihilator_iff d R _).mpr
    rw [multiplierMap_reconstruct Φ R S hfit]
    exact (hexact _).mpr ⟨windowPolynomial S b, rfl⟩

/-- The dimension identity `dim V_R(d) + |S| = |R|` in Theorem 2.2 (`thm:descent`).
Together with `translatedSpan_eq_ker`, this is equation `eq:filter-dimension`.
The additive form also covers an empty eroded window. -/
theorem translatedSpan_finrank_add (d : Configuration ℚ) (Φ : Laurent) (hΦ : Φ ≠ 0)
    (R S : Finset Lattice)
    (hexact : ∀ f : Laurent, act f d = 0 ↔ Φ ∣ f)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S) :
    Module.finrank ℚ (translatedSpan d R) + S.card = R.card := by
  classical
  have hinj : Function.Injective
      ((dotProductEquiv ℚ R).toLinearMap.comp (multiplierMap Φ R S)) := by
    intro a b hab
    apply multiplierMap_injective Φ hΦ R S hfit
    exact (dotProductEquiv ℚ R).injective hab
  have hrank : Module.finrank ℚ (translatedSpan d R).dualAnnihilator = S.card := by
    rw [dualAnnihilator_eq_multiplier_range d Φ R S hexact hfit,
      LinearMap.finrank_range_of_inj hinj]
    simp
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (translatedSpan d R)
  simpa only [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hsum

/-- The map `F : ℚ^R → ℚ^S` induced by the Laurent operator.
Defined in Theorem 2.2 (`thm:descent`); `hS` ensures every sampled input lies in `R`. -/
noncomputable def localFilter (Φ : Laurent) (R S : Finset Lattice)
    (hS : ∀ z ∈ S, ∀ a ∈ Φ.coeff.support, z + a ∈ R) : (R → ℚ) →ₗ[ℚ] (S → ℚ) where
  toFun p z := ∑ a : Φ.coeff.support, Φ.coeff a * p ⟨z.1 + a.1, hS z.1 z.2 a.1 a.2⟩
  map_add' p q := by
    classical
    funext z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a p := by
    classical
    funext z
    simp [Finset.mul_sum, mul_assoc, mul_comm]

/-- Filtering an occurring input pattern gives the corresponding output pattern.
This is shift commutation in the proof of Theorem 2.2 (`thm:descent`). -/
theorem localFilter_patternAt (Φ : Laurent) (R S : Finset Lattice)
    (hS : ∀ z ∈ S, ∀ a ∈ Φ.coeff.support, z + a ∈ R)
    (c : Configuration ℚ) (u : Lattice) :
    localFilter Φ R S hS (patternAt c R u) = patternAt (act Φ c) S u := by
  classical
  funext z
  simp only [localFilter, LinearMap.coe_mk, AddHom.coe_mk, patternAt, act_apply, Finsupp.sum]
  rw [← Finset.sum_attach Φ.coeff.support (fun a => Φ.coeff a * c (z.1 + u + a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [show z.1 + a.1 + u = z.1 + u + a.1 by abel]

/-- The image of all occurring input patterns is exactly the output pattern set.
This is `F(Pat_c(R)) = Pat_{Φ(T)c}(S)` in Theorem 2.2 (`thm:descent`). -/
theorem localFilter_patterns_image (Φ : Laurent) (R S : Finset Lattice)
    (hS : ∀ z ∈ S, ∀ a ∈ Φ.coeff.support, z + a ∈ R) (c : Configuration ℚ) :
    localFilter Φ R S hS '' patterns c R = patterns (act Φ c) S := by
  ext p
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (localFilter_patternAt Φ R S hS c u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨patternAt c R u, ⟨u, rfl⟩, localFilter_patternAt Φ R S hS c u⟩

/-- The transpose of the local filter is multiplication by `Φ`, after identifying
coefficient vectors with their dot-product functionals. This is the transpose
identity in the proof of Theorem 2.2 (`thm:descent`). -/
theorem localFilter_transpose (Φ : Laurent) (R S : Finset Lattice)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S)
    (hS : ∀ z ∈ S, ∀ a ∈ Φ.coeff.support, z + a ∈ R) :
    (localFilter Φ R S hS).dualMap.comp (dotProductEquiv ℚ S).toLinearMap =
      (dotProductEquiv ℚ R).toLinearMap.comp (multiplierMap Φ R S) := by
  classical
  apply LinearMap.ext
  intro b
  apply LinearMap.ext
  intro p
  let c : Configuration ℚ := fun z => if hz : z ∈ R then p ⟨z, hz⟩ else 0
  have hp : patternAt c R 0 = p := by
    funext z
    simp [patternAt, c, z.2]
  change dotProductEquiv ℚ S b (localFilter Φ R S hS p) =
    dotProductEquiv ℚ R (multiplierMap Φ R S b) p
  rw [← hp, localFilter_patternAt, dotProduct_patternAt, dotProduct_patternAt,
    multiplierMap_reconstruct Φ R S hfit, mul_comm Φ, act_mul]

/-- The translated restrictions of `d` span the full kernel of the local filter.
This is equation `eq:full-kernel` in Theorem 2.2 (`thm:descent`). -/
theorem translatedSpan_eq_ker (d : Configuration ℚ) (Φ : Laurent)
    (R S : Finset Lattice)
    (hexact : ∀ f : Laurent, act f d = 0 ↔ Φ ∣ f)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S)
    (hS : ∀ z ∈ S, ∀ a ∈ Φ.coeff.support, z + a ∈ R) :
    translatedSpan d R = LinearMap.ker (localFilter Φ R S hS) := by
  classical
  apply Subspace.dualAnnihilator_inj.mp
  rw [dualAnnihilator_eq_multiplier_range d Φ R S hexact hfit,
    ← localFilter_transpose Φ R S hfit hS,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.range_dualMap_eq_dualAnnihilator_ker]

/-- The linear-algebra and fiber-counting argument of Theorem 2.2 (`thm:descent`).
Its geometric hypothesis is supplied by Lemma 2.1 for rectangular windows. -/
private theorem complexity_descent_of_supported_multiples
    (c : Configuration ℚ) (hc : FiniteRange c) (x y : Configuration ℚ)
    (hx : ∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D)
    (hy : ∀ D : Finset Lattice, patternAt y D 0 ∈ patterns c D)
    (Φ : Laurent) (hΦ : Φ ≠ 0) (R S : Finset Lattice)
    (hexact : ∀ f : Laurent, act f (x - y) = 0 ↔ Φ ∣ f)
    (hfit : ∀ g : Laurent, (Φ * g).coeff.support ⊆ R ↔ g.coeff.support ⊆ S)
    (hS : ∀ z ∈ S, ∀ a ∈ Φ.coeff.support, z + a ∈ R) :
    complexity (act Φ c) S + R.card ≤ complexity c R + S.card := by
  let F := localFilter Φ R S hS
  have hd : act Φ (x - y) = 0 := (hexact Φ).mpr (dvd_refl Φ)
  have hle : translatedSpan (x - y) R ≤ Submodule.span ℚ (fiberDifferences F (patterns c R)) := by
    apply Submodule.span_le.mpr
    rintro p ⟨u, rfl⟩
    apply Submodule.subset_span
    refine ⟨patternAt x R u, patternAt_mem_of_language hx R u,
      patternAt y R u, patternAt_mem_of_language hy R u, ?_, rfl⟩
    have heq : act Φ x = act Φ y := sub_eq_zero.mp (by rwa [← act_config_sub])
    simp only [F, localFilter_patternAt, heq]
  have hkernel := translatedSpan_eq_ker (x - y) Φ R S hexact hfit hS
  rw [hkernel] at hle
  have hdim := Submodule.finrank_mono hle
  have hbudget := finite_fiber_budget (K := ℚ) F (patterns_finite hc R)
  have hrank := translatedSpan_finrank_add (x - y) Φ hΦ R S hexact hfit
  rw [hkernel] at hrank
  have himage : F '' patterns c R = patterns (act Φ c) S :=
    localFilter_patterns_image Φ R S hS c
  rw [himage] at hbudget
  change Module.finrank ℚ (Submodule.span ℚ (fiberDifferences F (patterns c R))) +
    complexity (act Φ c) S ≤ complexity c R at hbudget
  omega

/-- Theorem 2.2 (`thm:descent`): exact complexity descent on a rectangle.
The orbit-closure hypotheses are expressed by their finite-pattern language
inclusion. The additive inequality avoids truncated subtraction and also
handles an empty rectangle or eroded window. -/
theorem exact_complexity_descent
    (c : Configuration ℚ) (hc : FiniteRange c) (x y : Configuration ℚ)
    (hx : ∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D)
    (hy : ∀ D : Finset Lattice, patternAt y D 0 ∈ patterns c D)
    (Φ : Laurent) (hΦ : Φ ≠ 0)
    (hexact : ∀ f : Laurent, act f (x - y) = 0 ↔ Φ ∣ f) (m n : ℕ) :
    complexity (act Φ c) (erodedWindow Φ hΦ (rectangle m n)) + (rectangle m n).card ≤
      complexity c (rectangle m n) + (erodedWindow Φ hΦ (rectangle m n)).card := by
  exact complexity_descent_of_supported_multiples c hc x y hx hy Φ hΦ
    (rectangle m n) (erodedWindow Φ hΦ (rectangle m n)) hexact
    (fun g => support_mul_subset_rectangle_iff Φ hΦ g m n)
    (fun z hz => (mem_erodedWindow Φ hΦ (rectangle m n) z).mp hz)

/-- Corollary 2.3 (`cor:line-descent`): an exact annihilator gives a positive
rectangle of smaller area on which the filtered configuration has low complexity.

The support-width argument applies to any nonzero exact filter of a nonzero
difference; in the paper it is used for the line polynomial of Theorem 4.1. -/
theorem exists_smaller_low_complexity_rectangle
    (c : Configuration ℚ) (hc : FiniteRange c) (x y : Configuration ℚ)
    (hx : ∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D)
    (hy : ∀ D : Finset Lattice, patternAt y D 0 ∈ patterns c D)
    (hd : x - y ≠ 0) (Φ : Laurent) (hΦ : Φ ≠ 0)
    (hexact : ∀ f : Laurent, act f (x - y) = 0 ↔ Φ ∣ f)
    (m n : ℕ) (hlow : complexity c (rectangle m n) ≤ m * n) :
    ∃ m' n' : ℕ, 0 < m' ∧ 0 < n' ∧ m' * n' < m * n ∧
      complexity (act Φ c) (rectangle m' n') ≤ m' * n' := by
  classical
  let S := erodedWindow Φ hΦ (rectangle m n)
  have hdesc := exact_complexity_descent c hc x y hx hy Φ hΦ hexact m n
  have hfiltered : FiniteRange (act Φ c) := finiteRange_act Φ hc
  have hlowS : complexity (act Φ c) S ≤ S.card := by
    change complexity (act Φ c) S + (rectangle m n).card ≤
      complexity c (rectangle m n) + S.card at hdesc
    rw [card_rectangle] at hdesc
    omega
  have hSne : S.Nonempty :=
    Finset.card_pos.mp ((complexity_pos hfiltered S).trans_le hlowS)
  have hann : act Φ (x - y) = 0 := (hexact Φ).mpr dvd_rfl
  obtain ⟨m', n', o, hm', hn', hsmall, hshape⟩ :=
    exists_smaller_rectangle_of_annihilator Φ hΦ (x - y) hd hann m n hSne
  refine ⟨m', n', hm', hn', hsmall, ?_⟩
  change complexity (act Φ c) (erodedWindow Φ hΦ (rectangle m n)) ≤
    (erodedWindow Φ hΦ (rectangle m n)).card at hlowS
  rw [hshape, complexity_translate_window,
    Finset.card_image_of_injective _ (fun a b hab => add_right_cancel hab),
    card_rectangle] at hlowS
  exact hlowS

end Nivat.Descent
