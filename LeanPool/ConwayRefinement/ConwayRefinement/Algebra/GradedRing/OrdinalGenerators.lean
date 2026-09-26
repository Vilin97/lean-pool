/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.LoweringDerivation.Mu
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Homogeneous generators of an ordinal-graded algebra

Let `A` (Lean `R`) be a commutative algebra over a field `E` graded by `NatOrdinal` (the ordinals
under the natural sum `⊕`), so that `A_i A_j ⊆ A_{i ⊕ j}`. Let `A_+ := ⨁_{β ≠ 0} A_β` be the ideal
of elements of positive degree; its square meets `A_β` in
`(A_+)² ∩ A_β = ∑_{i ⊕ j = β, i, j ≠ 0} A_i A_j` (the decomposable elements of degree `β`; Lean
`decomposableAt 𝒜 β`). A *minimal system of homogeneous generators* is a family of homogeneous
elements `x i ∈ A_{wt i}` of positive degree whose members of each degree `β` are linearly
independent modulo `(A_+)² ∩ A_β` and span `A_β` modulo it — a basis of a complement of
`(A_+)² ∩ A_β` in `A_β` for every `β ≠ 0`. Evaluation `E[X_i] → A`, `X_i ↦ x i`, is then graded
for the degrees `deg X_i = wt i` (Mathlib's `IsWeightedHomogeneous wt`) and surjective, by
well-founded induction on the degree. Whether it is injective is the question whether `A` is a
polynomial algebra on the generators; this file only names the homogeneous pieces of that question,
`InjectiveAt β` (evaluation is injective in degree `β`), and shows that they assemble into the
injectivity of evaluation. The finite-degree theory of
`ConwayRefinement.Algebra.LoweringDerivation` is the case of degrees in `ℕ`.
-/

universe u v w o

open LoweringDerivation MvPolynomial

public noncomputable section

namespace OrdinalGraded

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]
variable (𝒜 : NatOrdinal.{o} → Submodule E R) [GradedAlgebra 𝒜]

/-! ### The square of the ideal of positive degree -/

/-- `(A_+)² ∩ A_β = ∑_{i ⊕ j = β, i, j ≠ 0} A_i A_j`, the square of the ideal of positive degree
in degree `β`. -/
def decomposableAt (β : NatOrdinal.{o}) : Submodule E R :=
  ⨆ (i : NatOrdinal.{o}) (j : NatOrdinal.{o}) (_ : i ≠ 0) (_ : j ≠ 0) (_ : i + j = β), 𝒜 i * 𝒜 j

omit [GradedAlgebra 𝒜] in
theorem decomposableAt_le {β : NatOrdinal.{o}} {N : Submodule E R}
    (h : ∀ i j : NatOrdinal.{o}, i ≠ 0 → j ≠ 0 → i + j = β → 𝒜 i * 𝒜 j ≤ N) :
    decomposableAt 𝒜 β ≤ N :=
  iSup_le fun i ↦ iSup_le fun j ↦ iSup_le fun hi ↦ iSup_le fun hj ↦ iSup_le fun hij ↦
    h i j hi hj hij

omit [GradedAlgebra 𝒜] in
theorem mul_mem_decomposableAt {i j : NatOrdinal.{o}} (hi : i ≠ 0) (hj : j ≠ 0) {a b : R}
    (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) : a * b ∈ decomposableAt 𝒜 (i + j) :=
  Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hi
    (Submodule.mem_iSup_of_mem hj (Submodule.mem_iSup_of_mem rfl (Submodule.mul_mem_mul ha hb)))))

/-- `(A_+)² ∩ A_β` lies in `A_β`. -/
theorem decomposableAt_le_degree (β : NatOrdinal.{o}) : decomposableAt 𝒜 β ≤ 𝒜 β :=
  decomposableAt_le 𝒜 fun i j _ _ hij ↦ by
    rw [← hij]
    exact Submodule.mul_le.mpr fun a ha b hb ↦ SetLike.mul_mem_graded ha hb

/-! ### Minimal systems of homogeneous generators -/

variable {ι : Type w} (wt : ι → NatOrdinal.{o}) (x : ι → R)

/-- A minimal system of homogeneous generators of an ordinal-graded algebra: homogeneous elements
`x i ∈ A_{wt i}` of positive degree whose members of degree `β` are linearly independent modulo
`(A_+)² ∩ A_β = ∑_{i ⊕ j = β, i, j ≠ 0} A_i A_j` and span `A_β` modulo it, for every `β ≠ 0`. -/
structure IsMinimalSystem : Prop where
  /-- Every generator has positive degree. -/
  ne_zero : ∀ i, wt i ≠ 0
  /-- `x i` is homogeneous of degree `wt i`. -/
  mem : ∀ i, x i ∈ 𝒜 (wt i)
  /-- The generators of degree `β` are linearly independent modulo `(A_+)² ∩ A_β`. -/
  independent : ∀ (β : NatOrdinal.{o}) (c : ι →₀ E), (∀ i ∈ c.support, wt i = β) →
    Finsupp.linearCombination E x c ∈ decomposableAt 𝒜 β → c = 0
  /-- The generators of degree `β` span `A_β` modulo `(A_+)² ∩ A_β`, for `β ≠ 0`. -/
  spans : ∀ β : NatOrdinal.{o}, β ≠ 0 → ∀ y ∈ 𝒜 β, ∃ c : ι →₀ E,
    (∀ i ∈ c.support, wt i = β) ∧ y - Finsupp.linearCombination E x c ∈ decomposableAt 𝒜 β

variable {𝒜 wt x}

/-! ### Graded evaluation -/

/-- Evaluation of a polynomial homogeneous of degree `β` (for `deg X_i = wt i`) at homogeneous
elements `x i ∈ A_{wt i}` lands in `A_β`. -/
theorem aeval_mem_of_forall_mem (hmem : ∀ i, x i ∈ 𝒜 (wt i)) {F : MvPolynomial ι E}
    {β : NatOrdinal.{o}} (hF : IsWeightedHomogeneous wt F β) : aeval x F ∈ 𝒜 β := by
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add p q hp hq ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | monomial d r hr =>
    rw [aeval_monomial, ← hr, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
    have h1 : ∏ i ∈ d.support, x i ^ d i ∈ 𝒜 (∑ i ∈ d.support, d i • wt i) :=
      SetLike.prod_mem_graded 𝒜 (fun i ↦ d i • wt i) (fun i ↦ x i ^ d i)
        fun i _ ↦ SetLike.pow_mem_graded _ (hmem i)
    have h2 := SetLike.mul_mem_graded (SetLike.algebraMap_mem_graded 𝒜 r) h1
    rwa [zero_add] at h2

/-- Evaluation at homogeneous `x i ∈ A_{wt i}` is graded: the degree-`β` component of `F(x)` is
the evaluation of the degree-`β` component of `F`. -/
theorem decompose_aeval (hmem : ∀ i, x i ∈ 𝒜 (wt i)) (F : MvPolynomial ι E) (β : NatOrdinal.{o}) :
    (DirectSum.decompose 𝒜 (aeval x F) β : R) =
      aeval x (weightedHomogeneousComponent wt β F) := by
  classical
  have hmem' : ∀ m : NatOrdinal.{o}, aeval x (weightedHomogeneousComponent wt m F) ∈ 𝒜 m :=
    fun m ↦ aeval_mem_of_forall_mem hmem
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := m) (φ := F))
  conv_lhs => rw [← sum_weightedHomogeneousComponent wt F,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp F), map_sum, DirectSum.decompose_sum,
    DirectSum.sum_apply, Submodule.coe_sum]
  rw [Finset.sum_eq_single β (fun m _ hne ↦ DirectSum.decompose_of_mem_ne 𝒜 (hmem' m) hne)
    fun hn ↦ ?_, DirectSum.decompose_of_mem_same 𝒜 (hmem' β)]
  have hz : weightedHomogeneousComponent wt β F = 0 := by
    apply not_not.mp
    intro hz
    exact hn ((weightedHomogeneousComponent_finsupp F).mem_toFinset.mpr hz)
  rw [hz, map_zero, DirectSum.decompose_zero, DirectSum.zero_apply, Submodule.coe_zero]

/-- A linear combination of the generators is the evaluation of the same combination of the
variables. -/
theorem aeval_linearCombination_X (c : ι →₀ E) :
    aeval x (Finsupp.linearCombination E (X : ι → MvPolynomial ι E) c) =
      Finsupp.linearCombination E x c := by
  rw [← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination]
  congr 2
  funext i
  exact aeval_X x i

/-- A linear combination of variables of degree `β` is homogeneous of degree `β`. -/
theorem isWeightedHomogeneous_linearCombination_X {β : NatOrdinal.{o}} (c : ι →₀ E)
    (hc : ∀ i ∈ c.support, wt i = β) :
    IsWeightedHomogeneous wt (Finsupp.linearCombination E (X : ι → MvPolynomial ι E) c) β := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ ?_
  rw [smul_eq_C_mul]
  have := (isWeightedHomogeneous_C wt (c i)).mul (isWeightedHomogeneous_X E wt i)
  rwa [zero_add, hc i hi] at this

/-! ### Generation -/

namespace IsMinimalSystem

variable (hx : IsMinimalSystem 𝒜 wt x)
include hx

omit hx [GradedAlgebra 𝒜] in
private theorem map_decomposableAt
    {S : Type*} [CommRing S] [Algebra E S]
    {ℬ : NatOrdinal.{o} → Submodule E S}
    (e : R ≃ₐ[E] S) (hgrade : ∀ (n : NatOrdinal.{o}) (r : R), r ∈ 𝒜 n ↔ e r ∈ ℬ n)
    {n : NatOrdinal.{o}} {r : R} (hr : r ∈ decomposableAt 𝒜 n) :
    e r ∈ decomposableAt ℬ n := by
  apply (decomposableAt_le 𝒜 fun i j hi hj hij ↦ ?_ :
    decomposableAt 𝒜 n ≤ (decomposableAt ℬ n).comap e.toLinearMap) hr
  apply Submodule.mul_le.mpr
  intro a ha b hb
  change e (a * b) ∈ decomposableAt ℬ n
  rw [show e (a * b) = e a * e b from map_mul e a b, ← hij]
  exact mul_mem_decomposableAt ℬ hi hj (hgrade i a |>.mp ha) (hgrade j b |>.mp hb)

omit hx [GradedAlgebra 𝒜] in
private theorem symm_mem_decomposableAt
    {S : Type*} [CommRing S] [Algebra E S]
    {ℬ : NatOrdinal.{o} → Submodule E S}
    (e : R ≃ₐ[E] S) (hgrade : ∀ (n : NatOrdinal.{o}) (r : R), r ∈ 𝒜 n ↔ e r ∈ ℬ n)
    {n : NatOrdinal.{o}} {s : S} (hs : s ∈ decomposableAt ℬ n) :
    e.symm s ∈ decomposableAt 𝒜 n := by
  apply (decomposableAt_le ℬ fun i j hi hj hij ↦ ?_ :
    decomposableAt ℬ n ≤ (decomposableAt 𝒜 n).comap e.symm.toLinearMap) hs
  apply Submodule.mul_le.mpr
  intro a ha b hb
  change e.symm (a * b) ∈ decomposableAt 𝒜 n
  rw [show e.symm (a * b) = e.symm a * e.symm b from map_mul e.symm a b, ← hij]
  exact mul_mem_decomposableAt 𝒜 hi hj
    ((hgrade i (e.symm a)).mpr (by simpa)) ((hgrade j (e.symm b)).mpr (by simpa))

omit [GradedAlgebra 𝒜] in
/-- An algebra equivalence preserving every homogeneous component carries minimal systems to
minimal systems. -/
theorem map_algEquiv
    {S : Type*} [CommRing S] [Algebra E S]
    {ℬ : NatOrdinal.{o} → Submodule E S}
    (e : R ≃ₐ[E] S) (hgrade : ∀ (n : NatOrdinal.{o}) (r : R), r ∈ 𝒜 n ↔ e r ∈ ℬ n) :
    IsMinimalSystem ℬ wt (fun i ↦ e (x i)) where
  ne_zero := hx.ne_zero
  mem i := (hgrade (wt i) (x i)).mp (hx.mem i)
  independent β c hc hmem := by
    apply hx.independent β c hc
    have hlc : e (Finsupp.linearCombination E x c) =
        Finsupp.linearCombination E (fun i ↦ e (x i)) c := by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        Finsupp.sum, Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul e (c i) (x i)
    have hmem' : e (Finsupp.linearCombination E x c) ∈ decomposableAt ℬ β := by
      rw [hlc]
      exact hmem
    simpa only [AlgEquiv.symm_apply_apply] using
      symm_mem_decomposableAt e hgrade hmem'
  spans β hβ y hy := by
    obtain ⟨c, hc, hmem⟩ := hx.spans β hβ (e.symm y)
      ((hgrade β (e.symm y)).mpr (by simpa))
    refine ⟨c, hc, ?_⟩
    have hlc : e (Finsupp.linearCombination E x c) =
        Finsupp.linearCombination E (fun i ↦ e (x i)) c := by
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
        Finsupp.sum, Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact map_smul e (c i) (x i)
    have hmem' := map_decomposableAt e hgrade hmem
    simpa only [map_sub, AlgEquiv.apply_symm_apply, hlc] using hmem'

omit [GradedAlgebra 𝒜] in
/-- No generator of a minimal system is zero: zero lies in `(A_+)² ∩ A_β`. -/
theorem apply_ne_zero (i : ι) : x i ≠ 0 := by
  intro h0
  have h := hx.independent (wt i) (Finsupp.single i 1) (fun j hj ↦ by
      rw [((Finsupp.mem_support_single j i 1).mp hj).1]) (by
      rw [Finsupp.linearCombination_single, one_smul, h0]
      exact zero_mem _)
  exact one_ne_zero (Finsupp.single_eq_zero.mp h)

/-- Evaluation of a polynomial homogeneous of degree `β` lands in `A_β`. -/
theorem aeval_mem {F : MvPolynomial ι E} {β : NatOrdinal.{o}} (hF : IsWeightedHomogeneous wt F β) :
    aeval x F ∈ 𝒜 β :=
  aeval_mem_of_forall_mem hx.mem hF

omit [GradedAlgebra 𝒜] in
/-- Every element of `A_β` is the evaluation of a weighted-homogeneous polynomial of weight `β`
at a minimal system relative to the family `𝒜`. -/
@[blueprint "lem:generate"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Weighted-homogeneous polynomial representatives")
  (statement := /--
    Let $E$ be a field, let $R$ be a commutative $E$-algebra, and let
    $(A_\alpha)_{\alpha\in\mathbf{On}}$ be a family of $E$-subspaces of $R$.
    Put
    \[
      D_\beta=\sum_{\substack{i\oplus j=\beta\\i,j\ne0}}A_iA_j.
    \]
    Let $(x_i,w_i)$ have positive weights, with $x_i\in A_{w_i}$. Suppose the
    $x_i$ of weight $\beta$ are independent modulo $D_\beta$ for every
    $\beta$ and span $A_\beta$ modulo $D_\beta$ whenever $\beta\ne0$.
    If every element of $A_0$ is a scalar from $E$, then every $y\in A_\beta$
    equals $F(x)$ for some $F\in E[X_i:i\in I]$ weighted-homogeneous of
    weight $\beta$.
  -/)
  (proof := /--
  Proceed by well-founded induction on $\beta$. At weight zero the hypothesis
  makes $y$ a constant polynomial value. At positive weight, write $y$ modulo
  $D_\beta$ as a linear combination of the weight-$\beta$ generators. Every
  product defining $D_\beta$ has two positive weights strictly below $\beta$,
  so induction represents both factors by weighted-homogeneous polynomials.
  Adding their products to the linear combination gives the required polynomial.
  -/)]
theorem exists_aeval_eq (h0 : GradeZeroScalars 𝒜) (β : NatOrdinal.{o}) :
    ∀ y ∈ 𝒜 β, ∃ F : MvPolynomial ι E, IsWeightedHomogeneous wt F β ∧ aeval x F = y := by
  induction β using WellFoundedLT.induction with
  | _ β ih =>
  intro y hy
  rcases eq_or_ne β 0 with rfl | hβ
  · obtain ⟨e, rfl⟩ := (gradeZeroScalars_iff 𝒜).mp h0 y hy
    exact ⟨C e, isWeightedHomogeneous_C wt e, aeval_C x e⟩
  · obtain ⟨c, hcw, hc⟩ := hx.spans β hβ y hy
    -- the elements of degree `β` that are values of homogeneous polynomials form a submodule
    -- containing `(A_+)² ∩ A_β`
    let N : Submodule E R :=
      { carrier := {z | ∃ F : MvPolynomial ι E, IsWeightedHomogeneous wt F β ∧ aeval x F = z}
        zero_mem' := ⟨0, isWeightedHomogeneous_zero E wt β, map_zero _⟩
        add_mem' := fun ⟨F, hF, hFz⟩ ⟨G, hG, hGz⟩ ↦
          ⟨F + G, hF.add hG, by rw [map_add, hFz, hGz]⟩
        smul_mem' := fun e _ ⟨F, hF, hFz⟩ ↦
          ⟨C e * F, by simpa using (isWeightedHomogeneous_C wt e).mul hF,
            by rw [map_mul, aeval_C, hFz, Algebra.smul_def]⟩ }
    have hD : decomposableAt 𝒜 β ≤ N := by
      refine decomposableAt_le 𝒜 fun i j hi hj hij ↦ Submodule.mul_le.mpr fun a ha b hb ↦ ?_
      have hi' : i < β := hij ▸ lt_add_of_pos_right i (pos_iff_ne_zero.mpr hj)
      have hj' : j < β := hij ▸ lt_add_of_pos_left j (pos_iff_ne_zero.mpr hi)
      obtain ⟨F, hF, hFa⟩ := ih i hi' a ha
      obtain ⟨G, hG, hGb⟩ := ih j hj' b hb
      exact ⟨F * G, hij ▸ hF.mul hG, by rw [map_mul, hFa, hGb]⟩
    obtain ⟨G, hG, hGz⟩ := hD hc
    refine ⟨G + Finsupp.linearCombination E (X : ι → MvPolynomial ι E) c,
      hG.add (isWeightedHomogeneous_linearCombination_X c hcw), ?_⟩
    rw [map_add, hGz, aeval_linearCombination_X, sub_add_cancel]

/-- Evaluation is surjective. -/
theorem aeval_surjective (h0 : GradeZeroScalars 𝒜) :
    Function.Surjective (aeval x : MvPolynomial ι E →ₐ[E] R) := by
  intro y
  induction y using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, map_zero _⟩
  | homogeneous z =>
    obtain ⟨F, -, hF⟩ := hx.exists_aeval_eq h0 _ z.1 z.2
    exact ⟨F, hF⟩
  | add y z hy hz =>
    obtain ⟨F, rfl⟩ := hy
    obtain ⟨G, rfl⟩ := hz
    exact ⟨F + G, map_add _ _ _⟩

end IsMinimalSystem

/-! ### Homogeneous polynomials of degree zero -/

omit [GradedAlgebra 𝒜] in
/-- For degrees `wt i ≠ 0`, a polynomial homogeneous of degree zero is a constant. -/
theorem eq_C_of_isWeightedHomogeneous_zero (hwt : ∀ i, wt i ≠ 0) {p : MvPolynomial ι E}
    (hp : IsWeightedHomogeneous wt p 0) : p = C (p.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · by_contra h
    have hw := hp h
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr (fun h ↦ hm h.symm)
    have hi' : m i ≠ 0 := Finsupp.mem_support_iff.mp hi
    rw [Finsupp.weight_apply, Finsupp.sum,
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ bot_le] at hw
    have h1 : wt i ≤ m i • wt i := by
      simpa using nsmul_le_nsmul_left (bot_le : (0 : NatOrdinal.{o}) ≤ wt i)
        (Nat.one_le_iff_ne_zero.mpr hi')
    exact hwt i (le_antisymm (h1.trans_eq (hw i hi)) bot_le)

/-! ### Injectivity degree by degree -/

variable (E wt x) in
/-- Evaluation is injective in degree `β`: `F = 0` is the only polynomial homogeneous of degree `β`
with `F(x) = 0`. -/
def InjectiveAt (β : NatOrdinal.{o}) : Prop :=
  ∀ F : MvPolynomial ι E, IsWeightedHomogeneous wt F β →
    (aeval x : MvPolynomial ι E →ₐ[E] R) F = 0 → F = 0

omit [GradedAlgebra 𝒜] in
theorem injectiveAt_iff (β : NatOrdinal.{o}) :
    InjectiveAt E wt x β ↔
      ∀ F : MvPolynomial ι E, IsWeightedHomogeneous wt F β →
        (aeval x : MvPolynomial ι E →ₐ[E] R) F = 0 → F = 0 :=
  Iff.rfl

omit [GradedAlgebra 𝒜] in
/-- In degree zero evaluation is injective: a homogeneous polynomial of degree zero is a scalar. -/
theorem injectiveAt_zero [Nontrivial R] (hwt : ∀ i, wt i ≠ 0) : InjectiveAt E wt x 0 := by
  intro F hF hF0
  rw [eq_C_of_isWeightedHomogeneous_zero hwt hF] at hF0 ⊢
  rw [aeval_C] at hF0
  rw [(algebraMap E R).injective (hF0.trans (map_zero _).symm), map_zero]

omit [GradedAlgebra 𝒜] in
/-- Injectivity in every ordinal degree follows from the zero, successor, and limit cases. -/
theorem injectiveAt_of_zero_successor_limit
    (hzero : InjectiveAt E wt x 0)
    (hsuccessor : ∀ α : NatOrdinal.{o}, α.constantCoeff ≠ 0 →
      (∀ β < α, InjectiveAt E wt x β) → InjectiveAt E wt x α)
    (hlimit : ∀ α : NatOrdinal.{o}, α ≠ 0 → α.constantCoeff = 0 →
      (∀ β < α, InjectiveAt E wt x β) → InjectiveAt E wt x α) :
    ∀ α, InjectiveAt E wt x α := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    rcases eq_or_ne α 0 with rfl | hα
    · exact hzero
    · by_cases hcc : α.constantCoeff = 0
      · exact hlimit α hα hcc ih
      · exact hsuccessor α hcc ih

/-- Injectivity in every degree gives injectivity of evaluation. -/
theorem aeval_injective_of_forall_injectiveAt (hmem : ∀ i, x i ∈ 𝒜 (wt i))
    (h : ∀ β, InjectiveAt E wt x β) :
    Function.Injective (aeval x : MvPolynomial ι E →ₐ[E] R) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro F hF
  have hcomp : ∀ m : NatOrdinal.{o}, aeval x (weightedHomogeneousComponent wt m F) = 0 := fun m ↦ by
    rw [← decompose_aeval hmem, hF, DirectSum.decompose_zero, DirectSum.zero_apply,
      Submodule.coe_zero]
  conv_lhs => rw [← sum_weightedHomogeneousComponent wt F,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp F)]
  exact Finset.sum_eq_zero fun m _ ↦ h m _
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := m) (φ := F)) (hcomp m)

/-! ### The linear part of a homogeneous polynomial -/

/-- A polynomial homogeneous of degree `β ≠ 0` evaluates at homogeneous generators of positive
degree to its linear part in the degree-`β` variables plus an element of `(A_+)² ∩ A_β`; the
linear coefficients are read off the polynomial. -/
@[blueprint "lem:homogeneous-polynomial-linear-term"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Linear part of a weighted-homogeneous polynomial")
  (statement := /--
    Let $E$ be a field and let $A=\bigoplus_{\alpha\in\mathbf{On}}A_\alpha$
    be a commutative $E$-algebra graded by the ordinals in a fixed universe,
    with multiplication graded by Hessenberg sum.  Let $(x_i)_{i\in I}$ satisfy
    $x_i\in A_{w(i)}$ with $w(i)\neq0$.  If
    $F\in E[X_i:i\in I]$ is weighted-homogeneous of degree $\beta\neq0$, then
    \[
     F(x)\equiv\sum_{w(i)=\beta}c_i x_i \bmod (A_+)^2\cap A_\beta,
    \]
    where $c_i$ is the coefficient of $X_i$ in $F$.
  -/)
  (proof := /--
  It suffices to inspect one monomial.  A monomial $cX_i$ of degree $\beta$
  contributes its linear term, while every other nonconstant monomial factors
  into two positive-degree monomials and therefore evaluates into
  $(A_+)^2\cap A_\beta$.
  -/)]
theorem exists_linear_part (hwt : ∀ i, wt i ≠ 0) (hmem : ∀ i, x i ∈ 𝒜 (wt i))
    {F : MvPolynomial ι E} {β : NatOrdinal.{o}} (hβ : β ≠ 0) (hF : IsWeightedHomogeneous wt F β) :
    ∃ c : ι →₀ E, (∀ i ∈ c.support, wt i = β) ∧
      aeval x F - Finsupp.linearCombination E x c ∈ decomposableAt 𝒜 β ∧
      ∀ i, c i = F.coeff (Finsupp.single i 1) := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => exact ⟨0, by simp, by simp, fun i ↦ by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨c, hcw, hc, hcoeff⟩ := ihp
    obtain ⟨c', hcw', hc', hcoeff'⟩ := ihq
    refine ⟨c + c', fun i hi ↦ ?_, ?_, fun i ↦ by
      rw [Finsupp.add_apply, hcoeff, hcoeff', AddMonoidAlgebra.coeff_add, Finsupp.add_apply]⟩
    · rcases Finset.mem_union.mp (Finsupp.support_add hi) with h | h
      · exact hcw i h
      · exact hcw' i h
    · rw [map_add, map_add]
      have := add_mem hc hc'
      convert this using 1
      abel
  | monomial d r hr =>
    by_cases hd : ∃ i, d = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := hd
      refine ⟨Finsupp.single i r, fun j hj ↦ ?_, ?_, fun j ↦ ?_⟩
      · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hj
        split_ifs at hj with h
        · subst h
          rw [Finsupp.weight_single, one_smul] at hr
          exact hr
        · exact absurd rfl hj
      · have hprod : (Finsupp.single i 1).prod (fun j k ↦ x j ^ k) = x i := by
          simp
        rw [Finsupp.linearCombination_single, aeval_monomial, hprod, Algebra.smul_def, sub_self]
        exact zero_mem _
      · rw [Finsupp.single_apply, coeff_monomial]
        by_cases h : i = j
        · subst h; simp
        · rw [ite_eq_right h, ite_eq_right]
          intro h'
          exact h (Finsupp.single_left_injective one_ne_zero h')
    · push Not at hd
      refine ⟨0, by simp, ?_, fun j ↦ by rw [Finsupp.coe_zero, Pi.zero_apply, coeff_monomial,
        ite_eq_right (hd j)]⟩
      rw [map_zero, sub_zero]
      -- `d` has at least two factors: split off one variable
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [map_zero] at hr
        exact hβ hr.symm
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
      have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      set d' := d - Finsupp.single i 1 with hd'
      have hdd' : d = Finsupp.single i 1 + d' := by
        rw [hd', add_comm, tsub_add_cancel_of_le]
        intro y
        rw [Finsupp.single_apply]
        split_ifs with hy
        · subst hy; exact Nat.pos_of_ne_zero hi'
        · exact Nat.zero_le _
      have hd'0 : d' ≠ 0 := by
        intro h
        rw [h, add_zero] at hdd'
        exact hd i hdd'
      have hw' : Finsupp.weight wt d' + wt i = β := by
        rw [← hr, hdd', map_add, Finsupp.weight_single, one_smul, add_comm]
      have hw'1 : Finsupp.weight wt d' ≠ 0 := by
        obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hd'0
        have hj' := Finsupp.mem_support_iff.mp hj
        intro h0
        rw [Finsupp.weight_apply, Finsupp.sum,
          Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ bot_le] at h0
        have h1 : wt j ≤ d' j • wt j := by
          simpa using nsmul_le_nsmul_left (bot_le : (0 : NatOrdinal.{o}) ≤ wt j)
            (Nat.one_le_iff_ne_zero.mpr hj')
        exact hwt j (le_antisymm (h1.trans_eq (h0 j hj)) bot_le)
      have hmono : monomial d r = X i * monomial d' r := by
        rw [hdd', add_comm, monomial_add_single, pow_one, mul_comm]
      rw [hmono, map_mul, aeval_X, ← hw', add_comm]
      exact mul_mem_decomposableAt 𝒜 (hwt i) hw'1 (hmem i)
        (aeval_mem_of_forall_mem hmem (isWeightedHomogeneous_monomial wt d' r rfl))

/-! ### Monomials of degree zero -/

omit [GradedAlgebra 𝒜] in
/-- For degrees `wt i ≠ 0`, only the constant monomial has degree zero. -/
theorem eq_zero_of_weight_eq_zero (hwt : ∀ i, wt i ≠ 0) {d : ι →₀ ℕ}
    (hd : Finsupp.weight wt d = 0) : d = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ bot_le] at hd
  have h1 : wt i ≤ d i • wt i := by
    simpa using nsmul_le_nsmul_left (bot_le : (0 : NatOrdinal.{o}) ≤ wt i)
      (Nat.one_le_iff_ne_zero.mpr hi')
  exact hwt i (le_antisymm (h1.trans_eq (hd i hi)) bot_le)

/-! ### Relations have no linear part and only variables of smaller degree -/

namespace IsMinimalSystem

variable (hx : IsMinimalSystem 𝒜 wt x)
include hx

/-- A homogeneous relation `F(x) = 0` of degree `β ≠ 0` has no linear monomial: its linear part is
a combination of the generators of degree `β` lying in `(A_+)² ∩ A_β`. -/
@[blueprint "lem:minimal-generators-relation-has-no-linear-term"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Vanishing of the linear part of a homogeneous relation")
  (statement := /--
    If $(x_i)_{i\in I}$ is a minimal system of homogeneous generators and the
    weighted-homogeneous polynomial $F$ of nonzero degree $\beta$ satisfies
    $F(x)=0$, then the coefficient of every linear monomial $X_i$ in $F$ is
    zero.
  -/)
  (proof := /--
  \ref{lem:homogeneous-polynomial-linear-term} places the linear
  combination of the degree-$\beta$ generators in
  $(A_+)^2\cap A_\beta$.  Their defining independence modulo this subspace
  kills every coefficient.
  -/)]
theorem coeff_single_eq_zero_of_aeval_eq_zero
    {F : MvPolynomial ι E} {β : NatOrdinal.{o}} (hβ : β ≠ 0)
    (hF : IsWeightedHomogeneous wt F β) (h0 : aeval x F = 0) (i : ι) :
    F.coeff (Finsupp.single i 1) = 0 := by
  obtain ⟨c, hcw, hc, hcoeff⟩ := exists_linear_part hx.ne_zero hx.mem hβ hF
  rw [h0, zero_sub, neg_mem_iff] at hc
  have := hx.independent β c hcw hc
  rw [← hcoeff, this, Finsupp.coe_zero, Pi.zero_apply]

/-- Every variable of a homogeneous relation `F(x) = 0` of degree `β ≠ 0` has degree below `β`. -/
@[blueprint "lem:variables-of-homogeneous-relation-have-smaller-degree"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Weights of variables in a homogeneous relation")
  (statement := /--
    Every variable occurring in a nonzero-degree weighted-homogeneous relation
    among a minimal system $(x_i)_{i\in I}$ of homogeneous generators has
    weight strictly below the degree of the relation.
  -/)
  (proof := /--
  Weighted homogeneity gives $w(i)\le\beta$.  Equality would make the monomial
  containing $X_i$ linear, contradicting
  \ref{lem:minimal-generators-relation-has-no-linear-term}.
  -/)]
theorem wt_lt_of_mem_vars_of_aeval_eq_zero {F : MvPolynomial ι E} {β : NatOrdinal.{o}} (hβ : β ≠ 0)
    (hF : IsWeightedHomogeneous wt F β) (h0 : aeval x F = 0) {i : ι} (hi : i ∈ F.vars) :
    wt i < β := by
  classical
  obtain ⟨d, hd, hdi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hdi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hdi
  have hdw : Finsupp.weight wt d = β := hF (mem_support_iff.mp hd)
  -- split off the variable `i`
  set d' := d - Finsupp.single i (d i) with hd'
  have hdd' : d = Finsupp.single i (d i) + d' := by
    rw [hd', add_comm, tsub_add_cancel_of_le]
    intro y
    rw [Finsupp.single_apply]
    split_ifs with hy
    · subst hy; exact le_rfl
    · exact Nat.zero_le _
  have hd'i : d' i = 0 := by rw [hd', Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.sub_self]
  have hsplit : d i • wt i + Finsupp.weight wt d' = β := by
    rw [← hdw]
    conv_rhs => rw [hdd']
    rw [map_add, Finsupp.weight_single]
  have hle : wt i ≤ β := by
    rw [← hsplit]
    calc wt i ≤ d i • wt i := by
          simpa using nsmul_le_nsmul_left (bot_le : (0 : NatOrdinal.{o}) ≤ wt i)
            (Nat.one_le_iff_ne_zero.mpr hdi')
      _ ≤ _ := NatOrdinal.le_add_right
  refine lt_of_le_of_ne hle fun heq ↦ ?_
  -- `wt i = β` forces `d = single i 1`, a linear monomial
  rw [heq] at hsplit
  have hd'0 : Finsupp.weight wt d' = 0 := by
    by_contra hne
    have : β < d i • β + Finsupp.weight wt d' := by
      calc β ≤ d i • β := by
            simpa using nsmul_le_nsmul_left (bot_le : (0 : NatOrdinal.{o}) ≤ β)
              (Nat.one_le_iff_ne_zero.mpr hdi')
        _ < d i • β + Finsupp.weight wt d' := lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hne)
    exact this.ne hsplit.symm
  have hd'zero : d' = 0 := eq_zero_of_weight_eq_zero hx.ne_zero hd'0
  rw [hd'0, add_zero] at hsplit
  have hdi1 : d i = 1 := by
    by_contra hne
    have h2 : 2 ≤ d i := by omega
    have : β < d i • β := by
      calc β < β + β := lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hβ)
        _ = 2 • β := (two_nsmul β).symm
        _ ≤ d i • β := nsmul_le_nsmul_left bot_le h2
    exact this.ne hsplit.symm
  have hdsingle : d = Finsupp.single i 1 := by rw [hdd', hd'zero, add_zero, hdi1]
  have := hx.coeff_single_eq_zero_of_aeval_eq_zero hβ hF h0 i
  rw [← hdsingle] at this
  exact mem_support_iff.mp hd this

end IsMinimalSystem

end OrdinalGraded
