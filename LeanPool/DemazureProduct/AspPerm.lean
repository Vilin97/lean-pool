/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.Utils
import LeanPool.DemazureProduct.SlipFace
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring

/-!
# Almost-sign-preserving permutations

This file defines almost-sign-preserving permutations, their inversion sets, associated slipfaces,
the Bruhat order, and some properties laying the groundwork for the Demazure product $\star$ and
residuals $\triangleleft$ and $\triangleright$. These three operations are not yet defined in
this file; that is deferred until `Submodular.lean`, where the bijection between $\mathrm{ASP}$ and
the set of submodular slipfaces is established. This corresponds roughly to Section 2, with some
bounded-difference material from Section 7, of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/

namespace LeanPool.DemazureProduct


/-- The inversion set $\operatorname{Inv} \tau = \{(u,v) \in \mathbb{Z}^2 : u < v \text{ and }
\tau(u) > \tau(v)\}$.
*Definition 2.5 (`defn:Inv`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def invSet (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  {(i,j) : ℤ × ℤ | i < j ∧ τ j < τ i}

/-- The southeast quadrant below value `m` and weakly to the right of index `n`. -/
def southeastSet (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | n ≤ k ∧ τ k < m }

/-- The northwest quadrant above value `m` and strictly to the left of index `n`. -/
def northwestSet (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | k < n ∧ m ≤ τ k }

/-- Reflect an integer function by the order-reversing involution `n ↦ -1 - n`. -/
abbrev flipFunc (f : ℤ → ℤ) : ℤ → ℤ := fun k => -1 - f (-1 - k)

lemma flip_quadrant (f : ℤ → ℤ) (a b : ℤ) :
  (-1 - ·) '' (southeastSet f a b) = northwestSet (flipFunc f) (-a) (-b) := by
  ext n
  simp only [Set.mem_image, southeastSet, northwestSet, Set.mem_ofPred_eq, flipFunc]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    constructor
    · omega
    · have hfm : f (-1 - (-1 - m)) = f m := by congr; omega
      rw [hfm]
      omega
  · intro ⟨hn1, hn2⟩
    exact ⟨-1 - n, ⟨by omega, by omega⟩, by ring_nf⟩

private lemma se_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (southeastSet τ m n).Finite → (southeastSet τ m' n').Finite := by
  let A := southeastSet τ m n
  let B := southeastSet τ m' n'
  let V := SetLike.coe (Finset.Ico n' n)
  let H₀ := SetLike.coe (Finset.Ico m m')
  let H := τ⁻¹' H₀
  change A.Finite → B.Finite
  intro fin_A
  have fin_V : V.Finite := Finset.finite_toSet _
  have fin_H₀ : H₀.Finite := Finset.finite_toSet _
  have fin_H : H.Finite := fin_H₀.preimage (Set.injOn_of_injective h_inj)
  have h : B ⊆ A ∪ (H ∪ V) := by
    intro k hk
    simp only [A, B] at hk ⊢
    unfold southeastSet at *
    by_cases k_lt_n : k < n
    · right; right
      simp only [V]
      simp only [Finset.coe_Ico, Set.mem_Ico, hk.1, k_lt_n, and_self]
    obtain k_ge_n : k ≥ n := by
      push Not at k_lt_n; exact k_lt_n
    by_cases τk_ge_m : τ k ≥ m
    · right; left
      simp only [H, H₀]
      simp only [Finset.coe_Ico, Set.mem_preimage, Set.mem_Ico, τk_ge_m, hk.2, and_self]
    simp_all
  refine Set.Finite.subset ?_ h
  exact Set.Finite.union fin_A (Set.Finite.union fin_H fin_V)

private lemma nw_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (northwestSet τ m n).Finite → (northwestSet τ m' n').Finite := by
  have hff : flipFunc (flipFunc τ) = τ := by
    funext n
    simp only [flipFunc, Int.reduceNeg, sub_sub_cancel]
  have hf_inj : Function.Injective (flipFunc τ) := fun x y h => by
    unfold flipFunc at h
    linarith [h_inj (show τ (-1 - x) = τ (-1 - y) from by omega)]
  have key : ∀ a b : ℤ, (northwestSet τ a b).Finite ↔
      (southeastSet (flipFunc τ) (-a) (-b)).Finite := fun a b => by
    have hq := flip_quadrant (flipFunc τ) (-a) (-b)
    simp only [hff, neg_neg] at hq
    rw [show northwestSet τ a b = (-1 - ·) '' southeastSet (flipFunc τ) (-a) (-b) from
      hq.symm]
    exact
      ⟨fun h => h.of_finite_image (Set.injOn_of_injective (fun x y h => by omega)),
        fun h => h.image _⟩
  rw [key m n, key m' n']
  exact se_finite_of_finite hf_inj (-m) (-n) (-m') (-n')

/-- The almost-sign-preserving condition: the set
$\{ n \in \mathbb{Z} : n \tau(n) < 0 \}$ is finite.

Equivalently, only finitely many integers change sign under `τ`. -/
def isAsp (τ : ℤ → ℤ) : Prop :=
  { n : ℤ | n * (τ n) < 0 }.Finite

lemma se_finite_of_asp {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n : ℤ) :
  isAsp τ → (southeastSet τ m n).Finite := by
  intro h_asp
  have h_se : (southeastSet τ 0 1).Finite := by
    unfold isAsp at h_asp
    have : southeastSet τ 0 1 ⊆ { n : ℤ | n * (τ n) < 0 } := by
      intro k hk
      simp only [southeastSet] at hk
      obtain ⟨k_pos, τk_neg⟩ := hk
      exact mul_neg_of_pos_of_neg k_pos τk_neg
    exact Set.Finite.subset h_asp this
  exact se_finite_of_finite h_inj 0 1 m n h_se

lemma nw_finite_of_asp {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n : ℤ) :
  isAsp τ → (northwestSet τ m n).Finite := by
  intro h_asp
  have h_nw : (northwestSet τ 1 0).Finite := by
    unfold isAsp at h_asp
    have : northwestSet τ 1 0 ⊆ { n : ℤ | n * (τ n) < 0 } := by
      intro k hk
      simp only[northwestSet] at hk
      obtain ⟨k_neg, τk_pos⟩ := hk
      exact mul_neg_of_neg_of_pos k_neg τk_pos
    exact Set.Finite.subset h_asp this
  exact nw_finite_of_finite h_inj 1 0 m n h_nw

lemma asp_of_finite_quadrants {τ : ℤ → ℤ} (h_inj : Function.Injective τ)
  {m n m' n' : ℤ} (fin_se : (southeastSet τ m n).Finite)
  (fin_nw : (northwestSet τ m' n').Finite) :
  isAsp τ := by
  unfold isAsp
  have : { n : ℤ | n * (τ n) < 0 } ⊆ (southeastSet τ 0 1) ∪ (northwestSet τ 1 0) := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    have := mul_neg_iff.mp hn
    rcases this with (pos_neg | neg_pos)
    · left
      unfold southeastSet
      simp; congr
    · right
      unfold northwestSet
      simp; congr
  refine Set.Finite.subset ?_ this
  apply Set.Finite.union
  · exact se_finite_of_finite h_inj m n 0 1 fin_se
  · exact nw_finite_of_finite h_inj m' n' 1 0 fin_nw

/-- An almost-sign-preserving permutation of `ℤ`, abbreviated ASP permutation.

This is the group $\mathrm{ASP}$ from
[An extended Demazure product](https://arxiv.org/abs/2206.14227), packaged in Lean as a function
together with proofs of bijectivity and the ASP condition. -/
structure AspPerm where
  /-- The underlying bijection of integers. -/
  func : ℤ → ℤ
  /-- The underlying function is bijective. -/
  bijective : Function.Bijective func
  /-- The underlying function is almost-sign-preserving. -/
  asp : isAsp func

instance : CoeFun AspPerm (fun _ => ℤ → ℤ) :=
  ⟨AspPerm.func⟩

namespace AspPerm
variable (τ : AspPerm)

lemma injective : Function.Injective τ.func := τ.bijective.injective

lemma surjective : Function.Surjective τ.func := τ.bijective.surjective

-- Lemmas for convenience, to handle edge cases involving i = j
lemma inv_iff_lt {i j : ℤ} (i_le_j : i ≤ j) :
  ⟨i, j⟩ ∈ invSet τ ↔  τ j < τ i := by
  rw [invSet]
  wlog i_lt_j : i < j
  · have i_eq_j : i = j := le_antisymm i_le_j (le_of_not_gt i_lt_j)
    rw [i_eq_j]; simp
  simp_all
lemma inv_iff_le {i j : ℤ} (i_lt_j : i < j) :
  ⟨i, j⟩ ∈ invSet τ ↔ τ j ≤ τ i := by
  constructor
  · intro ij_inv
    exact le_of_lt ij_inv.2
  · intro τ_j_le_i
    have : τ j ≠ τ i := by
      intro heq
      apply τ.injective at heq
      rw [heq] at i_lt_j; exact lt_irrefl i i_lt_j
    exact ⟨i_lt_j, lt_of_le_of_ne τ_j_le_i this⟩

lemma ext {σ τ : AspPerm} : σ = τ ↔ σ.func = τ.func := by
  constructor
  · intro h; rw [h]
  · intro h; cases σ; cases τ; congr

/-- Composition of ASP permutations. -/
def mul (σ τ : AspPerm) : AspPerm where
  func := Function.comp σ.func τ.func
  bijective :=
    Function.Bijective.comp σ.bijective τ.bijective
  asp := by
    have : {n | n * (σ (τ n)) < 0}
      ⊆ {n | n * (τ n) < 0} ∪ {n | (τ n) * (σ (τ n)) < 0} ∪ { n | τ n = 0}:= by
      intro n hn
      by_cases h0 : τ n = 0
      · simp_all
      by_cases hτ : n * τ n < 0
      · simp_all
      by_cases hσ : τ n * σ (τ n) < 0
      · simp_all
      exfalso
      push Not at hτ hσ
      let C := (τ n) ^ 2
      have hC_pos : C > 0 := by
        simp only [C]
        exact pow_two_pos_of_ne_zero h0
      have hC_nonneg : n * σ (τ n) * C ≥ 0 := by
        have hprod := mul_nonneg hσ hτ
        linarith
      have hC_neg : n * σ (τ n) * C < 0 :=
        mul_neg_of_neg_of_pos hn hC_pos
      exact not_lt_of_ge hC_nonneg hC_neg
    refine Set.Finite.subset ?_ this
    have h_pre : Set.Finite {n | τ n * σ (τ n) < 0} := by
      rw [show {n | τ n * σ (τ n) < 0} = τ ⁻¹' {n | n * σ n < 0} by
        simp_all]
      exact Set.Finite.preimage (Set.injOn_of_injective τ.injective) σ.asp
    have h_zero : Set.Finite {n | τ n = 0} := by
      rw [show {n | τ n = 0} = τ ⁻¹' ({0} : Set ℤ) by
        ext n
        simp]
      exact Set.Finite.preimage (Set.injOn_of_injective τ.injective) (Set.finite_singleton 0)
    exact Set.Finite.union (Set.Finite.union τ.asp h_pre) h_zero

/-- The inverse ASP permutation. -/
noncomputable def inv (τ : AspPerm) : AspPerm where
  func := Function.invFun τ.func
  bijective := by
    have hR : Function.RightInverse (Function.invFun τ.func) τ.func :=
      Function.rightInverse_invFun τ.surjective
    have hL : Function.LeftInverse (Function.invFun τ.func) τ.func :=
      Function.leftInverse_invFun τ.injective
    exact ⟨hR.injective, hL.surjective⟩
  asp := by
    refine Set.Finite.of_preimage ?_ τ.surjective
    suffices (τ.func ⁻¹' {n | n * Function.invFun τ.func n < 0}) = {n | n * τ n < 0} by
      rw [this]
      exact τ.asp
    ext n
    have := Function.leftInverse_invFun τ.injective n
    simp only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq, this, mul_comm]

/-- The identity ASP permutation. -/
def id : AspPerm where
  func := _root_.id
  bijective := ⟨Function.injective_id, Function.surjective_id⟩
  asp := by
    have : {n:ℤ | n * _root_.id n < 0} = ∅ := by
      ext n; simp only [id_eq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact mul_self_nonneg n
    unfold isAsp; simp_all

noncomputable instance : Group AspPerm where
  mul := mul
  inv := inv
  one := id
  mul_assoc := by intros a b c; rfl
  one_mul := by intro a; rfl
  mul_one := by intro a; rfl
  inv_mul_cancel := by
    intro τ
    apply (ext).2
    funext n
    change Function.invFun τ.func (τ.func n) = n
    exact Function.leftInverse_invFun τ.injective n

/-- Ordinary multiplication of ASP permutations is function composition. -/
@[simp] lemma mul_apply (σ τ : AspPerm) (n : ℤ) : (σ * τ) n = σ (τ n) := rfl

@[simp] lemma inv_mul_cancel_eval (n : ℤ) : τ⁻¹ (τ n) = n := by
  change Function.invFun τ.func (τ.func n) = n
  exact Function.leftInverse_invFun τ.injective n

@[simp] lemma mul_inv_cancel_eval (n : ℤ) : τ (τ⁻¹ n) = n := by
  change τ.func (Function.invFun τ.func n) = n
  exact Function.rightInverse_invFun τ.surjective n

lemma se_finite (a b : ℤ) : (southeastSet τ a b).Finite :=
  se_finite_of_asp τ.injective a b τ.asp

lemma nw_finite (a b : ℤ) : (northwestSet τ a b).Finite :=
  nw_finite_of_asp τ.injective a b τ.asp

/-- The finite southeast quadrant for an ASP permutation. -/
noncomputable def seFinset (a b : ℤ) : Finset ℤ := (τ.se_finite a b).toFinset

@[simp] lemma mem_se (a b n : ℤ) : n ∈ (τ.seFinset a b) ↔ n ≥ b ∧ τ n < a := by
  unfold seFinset
  simp [southeastSet]

/-- The finite northwest quadrant for an ASP permutation. -/
noncomputable def nwFinset (a b : ℤ) : Finset ℤ := (τ.nw_finite a b).toFinset

@[simp] lemma mem_nw (a b n : ℤ) : n ∈ (τ.nwFinset a b) ↔ n < b ∧ τ n ≥ a := by
  unfold nwFinset
  simp [northwestSet]

lemma inv_set_inverse (u v : ℤ) :
    ⟨u, v⟩ ∈ invSet τ ↔ ⟨τ v, τ u⟩ ∈ invSet τ⁻¹.func := by
  constructor
  · intro h
    obtain ⟨u_lt_v, τv_lt_τu⟩ := h
    use τv_lt_τu
    simpa
  · intro h
    obtain ⟨τv_lt_τu, u_lt_v⟩ := h
    simp only [inv_mul_cancel_eval] at u_lt_v
    exact ⟨u_lt_v, τv_lt_τu⟩

/-- Reverse an inversion box through an ASP permutation. -/
def revMap : ℤ × ℤ → ℤ × ℤ := fun ⟨i, j⟩ => ⟨τ j, τ i⟩

/-- The slipface associated to an ASP permutation is defined by
$s_\tau(a,b) = \#\{n \geq b : \tau(n) < a\}$, in the notation of
*Equation (4)* (`eq:sa`) in [An extended Demazure product](https://arxiv.org/abs/2206.14227).
In the repository, this is denoted as `τ.s_raw a b`. -/
private noncomputable def s_raw (a b : ℤ) : ℤ := ↑(southeastSet τ a b).ncard

/-- The companion counting function $s_{\tau^{-1}}(b,a)$.

In Lean this is written `τ.s'_raw b a`; later `dual_inverse_raw` identifies it with
`(τ⁻¹).s_raw`. -/
private noncomputable def s'_raw (b a : ℤ) : ℤ := ↑(northwestSet τ a b).ncard

private lemma dual_inverse_raw : τ.s'_raw = (τ⁻¹).s_raw := by
  funext b a
  calc
    τ.s'_raw b a = (northwestSet τ a b).ncard := by rfl
    _ = ( τ.func '' (northwestSet τ a b)).ncard := by
      rw [Set.ncard_image_of_injective (northwestSet τ a b) τ.injective]
    _ = (southeastSet τ⁻¹.func b a).ncard := by
      congr
      ext n
      constructor
      · intro h; unfold southeastSet
        rcases h with ⟨m, hm, rfl⟩; simp only [Set.mem_ofPred_eq, inv_mul_cancel_eval]
        exact ⟨hm.2, hm.1⟩
      · intro h
        use τ⁻¹ n
        unfold northwestSet; unfold southeastSet at h
        simp_all
    _ = (τ⁻¹).s_raw b a := by rfl

private lemma flip_bij (τ : AspPerm) : Function.Bijective (flipFunc τ.func) := by
  constructor
  · intro x y h; simp only [sub_right_inj, Int.reduceNeg] at h
    apply τ.injective at h
    omega
  · intro y
    use -1 - τ⁻¹ (-1 - y)
    simp only [flipFunc, Int.reduceNeg, sub_sub_cancel, mul_inv_cancel_eval]

private def flip : AspPerm := {
  func := fun n => -1 - τ (-1 - n)
  bijective := flip_bij τ
  asp := by
    let f := flipFunc τ
    let g := fun n => -1 - n
    change isAsp f
    have hinj : Function.Injective f := (flip_bij τ).injective
    have : g '' (southeastSet τ 0 0) = northwestSet f 0 0 := by
      exact flip_quadrant τ 0 0
    have nw_finite : (northwestSet f 0 0).Finite := by
      rw [← this]
      apply Set.Finite.image g
      exact se_finite_of_asp τ.injective 0 0 τ.asp
    have : g '' (southeastSet f 0 0) = northwestSet τ 0 0 := by
      have h := flip_quadrant f 0 0
      have : flipFunc f = τ := by
        funext n
        simp only [flipFunc, Int.reduceNeg, sub_sub_cancel, f]
      rw [this] at h
      exact h
    have se_finite : (southeastSet f 0 0).Finite := by
      have h : (g '' (southeastSet f 0 0)).Finite := by
        rw [this]
        exact nw_finite_of_asp τ.injective 0 0 τ.asp
      have h_inj : Set.InjOn g (southeastSet f 0 0) := by
        intro x _ y _ h
        linarith
      exact Set.Finite.of_finite_image h h_inj
    exact asp_of_finite_quadrants hinj se_finite nw_finite
}

private lemma flip_inv : τ.flip⁻¹ = τ⁻¹.flip := by
  simp only [ext]; ext n
  suffices τ.flip (τ.flip⁻¹ n) = τ.flip (τ⁻¹.flip n) by
    exact τ.flip.injective this
  simp
  dsimp [AspPerm.flip]
  simp

private lemma flip_flip : τ.flip.flip = τ := by
  suffices ∀ n, τ.flip.flip n = τ n by
    simp only [ext]; funext n; exact this n
  intro n
  simp only [flip, Int.reduceNeg, sub_sub_cancel]

private lemma flip_s (a b : ℤ) : τ.flip.s_raw a b = τ.s'_raw (-b) (-a) := by
  unfold AspPerm.s_raw AspPerm.s'_raw
  let A := southeastSet τ.flip a b
  let B := northwestSet τ (-a) (-b)
  suffices A.ncard = B.ncard by congr
  have hflip : flipFunc τ.flip = τ := by
    funext n
    simp only [flipFunc, Int.reduceNeg, flip, sub_sub_cancel]
  have himage : (-1 - ·) '' A = B := by
    dsimp [A, B]
    simpa [hflip] using (flip_quadrant τ.flip a b)
  have himage_card : ((-1 - ·) '' A).ncard = A.ncard :=
    Set.ncard_image_of_injective A (fun x y h => by omega)
  simp_all

/-- The shift $\chi_\tau = s_\tau(0,0) - s_{\tau^{-1}}(0,0)$.

[An extended Demazure product](https://arxiv.org/abs/2206.14227) writes this as
$\chi_\tau$; Lean writes it as `τ.χ`. -/
noncomputable def χ : ℤ := τ.s_raw 0 0 - τ.s'_raw 0 0

private lemma s_eq_se_card_raw (a b : ℤ) : τ.s_raw a b = (τ.seFinset a b).card := by
  unfold AspPerm.s_raw seFinset
  rw [Set.ncard_eq_toFinset_card _ (τ.se_finite a b)]

private lemma s_nonneg_raw (a b : ℤ) : τ.s_raw a b ≥ 0 := by
  unfold s_raw
  exact Nat.cast_nonneg _

private lemma s'_eq_nw_card_raw (b a : ℤ) : τ.s'_raw b a = (τ.nwFinset a b).card := by
  unfold AspPerm.s'_raw nwFinset
  rw [Set.ncard_eq_toFinset_card _ (τ.nw_finite a b)]

-- Helper: the number of elements of se(a',b) \ se(a,b) equals the number of
-- elements of Ico a a' whose τ-preimage is ≥ b, via the bijection k ↦ τ k.
private lemma se_diff_card (a a' b : ℤ) :
    ((τ.seFinset a' b) \ (τ.seFinset a b)).card =
      ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
  apply Finset.card_bij (fun k _ => τ k)
  · simp_all
  · intro k₁ _ k₂ _ h; exact τ.injective h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    obtain ⟨⟨x_ge_a, x_lt_a'⟩, τinv_ge_b⟩ := hx
    refine ⟨τ⁻¹ x, ?_, τ.mul_inv_cancel_eval x⟩
    simp_all

private lemma a_move_up_raw (a a' b : ℤ) (a_le_a' : a ≤ a') :
    τ.s_raw a' b = τ.s_raw a b + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
  have h_sub : τ.seFinset a b ⊆ τ.seFinset a' b := fun k hk => by
    simp only [mem_se] at *; exact ⟨hk.1, lt_of_lt_of_le hk.2 a_le_a'⟩
  suffices (τ.seFinset a' b).card
    = (τ.seFinset a b).card + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card by
    have hcard : ((τ.seFinset a' b).card : ℤ) =
        (τ.seFinset a b).card + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
      exact_mod_cast this
    rw [τ.s_eq_se_card_raw, τ.s_eq_se_card_raw]
    omega
  rw [← se_diff_card τ a a' b]
  have h_disj : Disjoint (τ.seFinset a b) (τ.seFinset a' b \ τ.seFinset a b) :=
    disjoint_sdiff_self_right
  have h_union : τ.seFinset a b ∪ τ.seFinset a' b \ τ.seFinset a b = τ.seFinset a' b :=
    Finset.union_sdiff_of_subset h_sub
  have h_card := Finset.card_union_of_disjoint h_disj
  rw [h_union] at h_card
  omega

private lemma b_move_up_raw (a b b' : ℤ) (b_le_b' : b ≤ b') :
  τ.s_raw a b' = τ.s_raw a b - ((Finset.Ico b b').filter (τ · < a)).card := by
  let A := τ.seFinset a b'
  let B := τ.seFinset a b
  let C := (Finset.Ico b b').filter (τ · < a)
  suffices B.card = A.card + C.card by
    unfold A B at this
    have hcard : ((τ.seFinset a b).card : ℤ) = (τ.seFinset a b').card + C.card := by
      exact_mod_cast this
    rw [τ.s_eq_se_card_raw, τ.s_eq_se_card_raw]
    linarith
  have h_disj : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro n hA hC
    simp only [A, mem_se] at hA
    simp only [Finset.mem_filter, Finset.mem_Ico, C] at hC
    linarith [hA.1, hC.1]
  have h_union : A ∪ C = B := by
    apply Finset.ext; intro n
    simp only [A,B,C, mem_se, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases h with (hA | hC)
      · simp only [hA.2]
        constructor
        · exact le_trans b_le_b' hA.1
        · exact True.intro
      · simp_all
    · intro hB
      by_cases n_ge_b' : b' ≤ n
      · left; exact ⟨n_ge_b', hB.2⟩
      simp_all
  rw [← h_union, Finset.card_union_of_disjoint h_disj]

/-- We have $s_\alpha(a+1,b) = s_\alpha(a,b) + \delta(\alpha^{-1}(a) \ge b)$.
This is Equation (13) (`eq:a+1`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
private lemma a_step_raw (a b : ℤ) : τ.s_raw (a + 1) b = τ.s_raw a b + (if τ⁻¹ a ≥ b then 1 else 0)
  := by
  rw [a_move_up_raw τ a (a + 1) b (by omega)]
  by_cases h : τ⁻¹ a ≥ b
  · have hfilt : ((Finset.Ico a (a + 1)).filter (τ⁻¹ · ≥ b)) = {a} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · intro ⟨⟨hge, hlt⟩, _⟩; omega
      · rintro rfl; exact ⟨⟨le_refl _, by omega⟩, h⟩
    simp only [ge_iff_le, hfilt, Finset.card_singleton, Nat.cast_one, if_pos h]
  · have hfilt : ((Finset.Ico a (a + 1)).filter (τ⁻¹ · ≥ b)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hge, hlt⟩, htau⟩
      have hxa : x = a := le_antisymm (Int.le_of_lt_add_one hlt) hge
      rw [hxa] at htau; exact h htau
    simp only [ge_iff_le, hfilt, Finset.card_empty, Nat.cast_zero, add_zero, if_neg h]


/-- We have $s_\alpha(a,b+1) = s_\alpha(a,b) - \delta(\alpha(b)<a)$.
This is Equation (12) (`eq:b+1`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
private lemma b_step_raw (a b : ℤ) : τ.s_raw a (b+1) = τ.s_raw a b - (if τ b < a then 1 else 0)
  := by
  have move_up := b_move_up_raw τ a b (b+1) (by omega)
  suffices {x ∈ Finset.Ico b (b + 1) | τ.func x < a}.card = if τ b < a then 1 else 0 by linarith
  by_cases h_lt : τ b < a
  · simp only [h_lt]
    suffices {x ∈ Finset.Ico b (b+1) | τ x < a} = {b} by
      simp_all
    ext n
    constructor
    · intro h; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton] at h ⊢
      linarith [h.1]
    · simp_all
  · have ge_a : τ b ≥ a := le_of_not_gt h_lt
    simp only [h_lt, ite_false, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x x_Ico
    obtain ⟨x_mem_Ico, τx_lt_a⟩ := Finset.mem_filter.mp x_Ico
    obtain ⟨x_ge_b, x_lt_b_plus_one⟩ := Finset.mem_Ico.mp x_mem_Ico
    have x_eq_b : x = b := le_antisymm (Int.le_of_lt_add_one x_lt_b_plus_one) x_ge_b
    rw [x_eq_b] at τx_lt_a
    linarith [ge_a, τx_lt_a]

/-- The key duality_raw formula for slipfaces of ASP permutations:
$s_\alpha(a,b) - s_{\alpha^{-1}}(b,a) = \chi_\alpha + a - b$.
This is Equation ($\dagger$) (`eq:saDuality`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
private theorem duality_raw (a b : ℤ) : τ.s_raw a b - (τ⁻¹).s_raw b a = τ.χ + a - b := by
  let h (a b : ℤ) := τ.s_raw a b - (τ⁻¹).s_raw b a - a + b
  have h_zero : h 0 0 = τ.χ := by
    simp only [h, AspPerm.χ]
    rw [dual_inverse_raw τ]
    omega
  have change_a : ∀ (a a' b : ℤ), h a' b = h a b := by
    intro a a' b
    wlog a_le_a' : a ≤ a' generalizing a a'
    · specialize this a' a (by omega)
      rw [this]
    calc
      h a' b = τ.s_raw a' b - τ⁻¹.s_raw b a' - a' + b := by rfl
      _ = τ.s_raw a b - τ⁻¹.s_raw b a' - a' + b
        + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
        rw [a_move_up_raw τ a a' b a_le_a']
        omega
      _ = τ.s_raw a b - τ⁻¹.s_raw b a - a' + b
        + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card
        + ((Finset.Ico a a').filter (τ⁻¹ · < b)).card := by
        rw [b_move_up_raw (τ⁻¹) b a a' (by omega)]
        omega
      _ = τ.s_raw a b - τ⁻¹.s_raw b a - a' + b
        + (Finset.Ico a a').card := by
        rw [← Utils.card_filter_helper (Finset.Ico a a') (τ⁻¹).func b]
        simp; omega
      _ = τ.s_raw a b - τ⁻¹.s_raw b a - a' + b + (a' - a) := by
        simp only [Int.card_Ico, Int.ofNat_toNat, Int.sub_nonneg, a_le_a', sup_of_le_left]
      _ = h a b := by linarith
  have change_b : ∀ (a b b' : ℤ), h a b' = h a b := by
    intro a b b'
    wlog b_le_b' : b ≤ b' generalizing b b'
    · specialize this b' b (by linarith [b_le_b'])
      rw [this]
    calc
      h a b' = τ.s_raw a b' - τ⁻¹.s_raw b' a - a + b' := by rfl
      _ = τ.s_raw a b - τ⁻¹.s_raw b' a - a + b'
        - ((Finset.Ico b b').filter (τ · < a)).card := by
        rw [b_move_up_raw τ a b b' b_le_b']
        omega
      _ = τ.s_raw a b - τ⁻¹.s_raw b a - a + b'
        - ((Finset.Ico b b').filter (τ · < a)).card
        - ((Finset.Ico b b').filter (τ · ≥ a)).card := by
        rw [a_move_up_raw (τ⁻¹) b b' a (by omega)]
        simp; omega
      _ = τ.s_raw a b - τ⁻¹.s_raw b a - a + b'
        - (Finset.Ico b b').card := by
        rw [← Utils.card_filter_helper (Finset.Ico b b') τ.func a]
        simp; omega
      _ = τ.s_raw a b - τ⁻¹.s_raw b a - a + b' - (b' - b) := by
        simp only [Int.card_Ico, Int.ofNat_toNat, Int.sub_nonneg, b_le_b', sup_of_le_left]
      _ = h a b := by linarith
  have : h a b = h 0 0 := by
    rw [change_a 0 a b, change_b 0 b 0]
  unfold h at this
  linarith

private lemma s_eq_raw (a b : ℤ) : τ.s_raw a b = (τ⁻¹).s_raw b a + τ.χ + a - b := by
  have := duality_raw τ a b
  omega

private lemma s_ge_raw (a b : ℤ) : τ.s_raw a b ≥ a - b + τ.χ := by
  rw [τ.s_eq_raw a b]
  linarith [τ⁻¹.s_nonneg_raw b a]

private lemma tend_zero_a_raw (b : ℤ) : ∃ a : ℤ, τ.s_raw a b = 0 := by
  by_cases h : τ.s_raw 0 b = 0
  · use 0
  · let S := Finset.image τ (τ.seFinset 0 b)
    have S_nonempty : S.Nonempty := by
      have h_ne : (southeastSet τ 0 b).ncard ≠ 0 := by
        simpa [AspPerm.s_raw] using h
      have h_nonempty : (southeastSet τ 0 b).Nonempty := Set.nonempty_of_ncard_ne_zero h_ne
      have h_se_nonempty : (τ.seFinset 0 b).Nonempty := by
        rcases h_nonempty with ⟨n, hn⟩
        exact ⟨n, by simpa [seFinset] using hn⟩
      unfold S
      exact Finset.image_nonempty.mpr h_se_nonempty
    let a := Finset.min' S S_nonempty
    have a_lt_0 : a < 0 := by
      have : a ∈ S := Finset.min'_mem S S_nonempty
      simp only [S, Finset.mem_image] at this
      obtain ⟨n, ⟨n_se, n_eq⟩⟩ := this
      simp_all
    use a
    suffices southeastSet τ (Finset.min' S S_nonempty) b = ∅ by
      have h_ncard : (southeastSet τ (Finset.min' S S_nonempty) b).ncard = 0 := by
        simp_all
      unfold AspPerm.s_raw
      exact_mod_cast h_ncard
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro n ⟨b_le_n, τn_lt_min⟩
    have : τ n < 0 := lt_trans τn_lt_min a_lt_0
    have : n ∈ τ.seFinset 0 b := (τ.mem_se 0 b n).mpr ⟨b_le_n, this⟩
    have : τ n ∈ S := Finset.mem_image.mpr ⟨n, this, rfl⟩
    have : a ≤ τ n := Finset.min'_le S (τ n) this
    exact lt_irrefl (τ n) <| lt_of_lt_of_le τn_lt_min this

private lemma tend_zero_b_raw (a : ℤ) : ∃ b : ℤ, τ.s_raw a b = 0 := by
  have := tend_zero_a_raw (τ := τ⁻¹.flip) (-a)
  obtain ⟨b, hb⟩ := this
  use -b
  rw [τ⁻¹.flip_s, τ⁻¹.dual_inverse_raw] at hb
  simpa using hb

private lemma s_nondec_raw {a a' : ℤ} (a_le_a' : a ≤ a') (b : ℤ) :
    τ.s_raw a b ≤ τ.s_raw a' b ∧
      (τ.s_raw a b = τ.s_raw a' b ↔ ∀ x : ℤ, a ≤ τ x → τ x < a' → x < b) := by
  rw [a_move_up_raw τ a a' b a_le_a']
  let S := {x ∈ Finset.Ico a a' | τ⁻¹ x ≥ b}
  constructor
  · simp_all
  -- Now handle the equality case
  suffices (∀ (x : ℤ), a ≤ τ.func x → τ.func x < a' → x < b) ↔ S.card = 0 by
    simp only [this]
    constructor <;> (intro; linarith)
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x xS
    specialize h (τ⁻¹ x)
    simp only [ge_iff_le, Finset.mem_filter, Finset.mem_Ico, S] at xS
    simp only [τ.mul_inv_cancel_eval, xS, forall_const] at h
    omega
  · intro hS x a_le τx_le
    specialize hS (τ x)
    simpa [S, a_le, τx_le] using hS

private lemma s_noninc_raw (a : ℤ) {b b' : ℤ} (b_le_b' : b ≤ b') :
    τ.s_raw a b ≥ τ.s_raw a b' ∧
      (τ.s_raw a b = τ.s_raw a b' ↔ ∀ x : ℤ, b ≤ x → x < b' → τ x ≥ a) := by
  let S := {x ∈ Finset.Ico b b' | τ x < a}
  have heq : τ.s_raw a b = τ.s_raw a b' + S.card := by
    rw [b_move_up_raw τ a b b' b_le_b']
    simp only [sub_add_cancel, S]
  constructor
  · simp_all
  · have : τ.s_raw a b = τ.s_raw a b' ↔ S.card = 0 := by
      simp_all
    rw [this, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    unfold S
    simp

/-- The slipface attached to `τ`.
[An extended Demazure product](https://arxiv.org/abs/2206.14227) writes its values as
$s_\tau(a,b)$; in Lean the corresponding value
is `τ.s_raw a b`, and `τ.s` packages the same data as a `SlipFace`. -/
noncomputable def s : SlipFace := {
  func := τ.s_raw
  χ := τ.χ
  a_step := by
    intro a b
    rw [τ.a_step_raw a b]
    by_cases h : τ⁻¹ a ≥ b <;> simp [h]
  b_step := by
    intro a b
    rw [τ.b_step_raw a b]
    by_cases h : τ b < a <;> simp [h]
  nonneg := τ.s_nonneg_raw
  ge_diff := τ.s_ge_raw
  small_a := by
    intro b
    obtain ⟨A, hA⟩ := τ.tend_zero_a_raw b
    use A
    intro a a_le_A
    have := (τ.s_nondec_raw a_le_A b).1
    rw [hA] at this
    apply le_antisymm this
    exact τ.s_nonneg_raw a b
  large_a := by
    intro b
    obtain ⟨A, hA⟩ := τ⁻¹.tend_zero_b_raw b
    use A; intro a a_ge_A
    have ha : τ⁻¹.s_raw b a = 0 := by
      apply le_antisymm
      · have := (τ⁻¹.s_noninc_raw b a_ge_A).1
        rwa [hA] at this
      · exact τ⁻¹.s_nonneg_raw b a
    rw [τ.s_eq_raw a b, ha]
    omega
  small_b := by
    intro a
    obtain ⟨B, hB⟩ := τ⁻¹.tend_zero_a_raw a
    use B; intro b b_le_B
    have hb : τ⁻¹.s_raw b a = 0 := by
      apply le_antisymm
      · have := (τ⁻¹.s_nondec_raw b_le_B a).1
        rwa [hB] at this
      · exact τ⁻¹.s_nonneg_raw b a
    rw [τ.s_eq_raw a b, hb]
    omega
  large_b := by
    intro a
    obtain ⟨B, hB⟩ := τ.tend_zero_b_raw a
    use B; intro b b_ge_B
    apply le_antisymm
    · have := (τ.s_noninc_raw a b_ge_B).1
      rwa [hB] at this
    · exact τ.s_nonneg_raw a b
}

/-! ### Basic properties of the slipface of a permutation -/

lemma s_eq_ncard (a b : ℤ) : τ.s a b = ↑(southeastSet τ a b).ncard := by rfl
lemma s'_eq_ncard (b a : ℤ) : (τ⁻¹).s b a = ↑(northwestSet τ a b).ncard := by
  change (τ⁻¹).s_raw b a = _
  rw [← dual_inverse_raw]
  rfl
lemma s_eq_se_card (a b : ℤ) : τ.s a b = (τ.seFinset a b).card := τ.s_eq_se_card_raw a b
lemma s_nonneg (a b : ℤ) : τ.s a b ≥ 0 := τ.s_nonneg_raw a b
lemma s_ge (a b : ℤ) : τ.s a b ≥ a - b + τ.χ := τ.s_ge_raw a b
lemma a_step (a b : ℤ) :
    τ.s (a + 1) b = τ.s a b + (if τ⁻¹ a ≥ b then 1 else 0) := τ.a_step_raw a b
lemma b_step (a b : ℤ) :
    τ.s a (b + 1) = τ.s a b - (if τ b < a then 1 else 0) := τ.b_step_raw a b

lemma s_noninc (a : ℤ) {b b' : ℤ} (b_le_b' : b ≤ b') :
    τ.s a b ≥ τ.s a b' ∧
      (τ.s a b = τ.s a b' ↔ ∀ x : ℤ, b ≤ x → x < b' → τ x ≥ a) := τ.s_noninc_raw a b_le_b'
lemma s_nondec {a a' : ℤ} (a_le_a' : a ≤ a') (b : ℤ) :
    τ.s a b ≤ τ.s a' b ∧
      (τ.s a b = τ.s a' b ↔ ∀ x : ℤ, a ≤ τ x → τ x < a' → x < b) := τ.s_nondec_raw a_le_a' b
lemma duality (a b : ℤ) : τ.s a b - (τ⁻¹).s b a = τ.χ + a - b := τ.duality_raw a b
lemma s_eq (a b : ℤ) : τ.s a b = (τ⁻¹).s b a + τ.χ + a - b := τ.s_eq_raw a b
lemma s'_eq (a b : ℤ) : (τ⁻¹).s a b = τ.s b a - τ.χ + a - b := by
  have := duality_raw τ b a
  dsimp [s]
  omega
lemma tend_zero_a (b : ℤ) : ∃ a : ℤ, τ.s a b = 0 := τ.tend_zero_a_raw b
lemma tend_zero_b (a : ℤ) : ∃ b : ℤ, τ.s a b = 0 := τ.tend_zero_b_raw a

lemma a_move_up (a a' b : ℤ) (a_le_a' : a ≤ a') :
    τ.s a' b = τ.s a b + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card :=
  τ.a_move_up_raw a a' b a_le_a'
lemma b_move_up (a b b' : ℤ) (b_le_b' : b ≤ b') :
    τ.s a b' = τ.s a b - ((Finset.Ico b b').filter (τ · < a)).card :=
  τ.b_move_up_raw a b b' b_le_b'

/-- The shift as a difference of southeast and northwest cardinalities. -/
lemma chi_eq_card : τ.χ = ((τ.seFinset 0 0).card : ℤ) - (τ.nwFinset 0 0).card := by
  dsimp [AspPerm.χ]
  rw [s_eq_se_card_raw, s'_eq_nw_card_raw]

-- Note: use of _raw definitions and statements should stop here

@[simp] lemma id_chi : AspPerm.id.χ = 0 := by
  have h_se : southeastSet AspPerm.id 0 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    dsimp [southeastSet, AspPerm.id] at hk
    omega
  have h_nw : northwestSet AspPerm.id 0 0 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    dsimp [northwestSet, AspPerm.id] at hk
    omega
  have := id.duality 0 0
  simp only [id.s_eq_ncard, id.s'_eq_ncard, h_se, h_nw, Set.ncard_empty] at this
  omega

lemma chi_dual : τ⁻¹.χ = - τ.χ := by
  have h1 := τ.duality 0 0
  have h2 := τ⁻¹.duality 0 0
  simp only [inv_inv] at h2
  omega

lemma chi_dual' : τ.χ = - (τ⁻¹).χ := by
  rw [← chi_dual τ⁻¹, inv_inv]

/-- Shift is additive under ordinary multiplication:
$\chi_{\alpha\beta} = \chi_\alpha + \chi_\beta$.
*Equation (16) (`eq:chiHom`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
lemma chi_mul (α β : AspPerm) : (α * β).χ = α.χ + β.χ := by
  -- Proof written by Codex.
  let A := Finset.image β (β.seFinset 0 0)
  let B := Finset.image β (β.nwFinset 0 0)
  let P := α.seFinset 0 0
  let Q := α.nwFinset 0 0
  let R := Finset.image β ((α * β).seFinset 0 0)
  let S := Finset.image β ((α * β).nwFinset 0 0)
  have hA (n : ℤ) : n ∈ A ↔ 0 ≤ β⁻¹ n ∧ n < 0 := by
    simp only [A, Finset.mem_image, mem_se, ge_iff_le]
    constructor
    · rintro ⟨m, ⟨hm, hβm⟩, rfl⟩
      simpa only [inv_mul_cancel_eval] using ⟨hm, hβm⟩
    · intro hn
      refine ⟨β⁻¹ n, ?_, by simp only [mul_inv_cancel_eval]⟩
      simpa only [mul_inv_cancel_eval] using hn
  have hB (n : ℤ) : n ∈ B ↔ β⁻¹ n < 0 ∧ 0 ≤ n := by
    simp only [B, Finset.mem_image, mem_nw, ge_iff_le]
    constructor
    · rintro ⟨m, ⟨hm, hβm⟩, rfl⟩
      simpa only [inv_mul_cancel_eval] using ⟨hm, hβm⟩
    · intro hn
      refine ⟨β⁻¹ n, ?_, by simp only [mul_inv_cancel_eval]⟩
      simpa only [mul_inv_cancel_eval] using hn
  have hR (n : ℤ) : n ∈ R ↔ 0 ≤ β⁻¹ n ∧ α n < 0 := by
    simp only [R, Finset.mem_image, mem_se, ge_iff_le, mul_apply]
    constructor
    · rintro ⟨m, ⟨hm, hαβm⟩, rfl⟩
      simpa only [inv_mul_cancel_eval] using ⟨hm, hαβm⟩
    · intro hn
      refine ⟨β⁻¹ n, ?_, by simp only [mul_inv_cancel_eval]⟩
      simpa only [mul_inv_cancel_eval] using hn
  have hS (n : ℤ) : n ∈ S ↔ β⁻¹ n < 0 ∧ 0 ≤ α n := by
    simp only [S, Finset.mem_image, mem_nw, ge_iff_le, mul_apply]
    constructor
    · rintro ⟨m, ⟨hm, hαβm⟩, rfl⟩
      simpa only [inv_mul_cancel_eval] using ⟨hm, hαβm⟩
    · intro hn
      refine ⟨β⁻¹ n, ?_, by simp only [mul_inv_cancel_eval]⟩
      simpa only [mul_inv_cancel_eval] using hn
  have hR_pos :
      R.filter (fun n => 0 ≤ n) = P.filter (fun n => 0 ≤ β⁻¹ n) := by
    ext n
    simp only [Finset.mem_filter, hR, P, mem_se, ge_iff_le]
    omega
  have hR_neg :
      R.filter (fun n => ¬ 0 ≤ n) = A.filter (fun n => α n < 0) := by
    ext n
    simp only [Finset.mem_filter, hR, hA]
    omega
  have hS_pos :
      S.filter (fun n => 0 ≤ n) = B.filter (fun n => 0 ≤ α n) := by
    ext n
    simp only [Finset.mem_filter, hS, hB]
    omega
  have hS_neg :
      S.filter (fun n => ¬ 0 ≤ n) = Q.filter (fun n => β⁻¹ n < 0) := by
    ext n
    simp only [Finset.mem_filter, hS, Q, mem_nw, ge_iff_le]
    omega
  have hP_cross :
      P.filter (fun n => ¬ 0 ≤ β⁻¹ n) = B.filter (fun n => α n < 0) := by
    ext n
    simp only [Finset.mem_filter, P, mem_se, ge_iff_le, hB]
    omega
  have hQ_cross :
      Q.filter (fun n => 0 ≤ β⁻¹ n) = A.filter (fun n => ¬ α n < 0) := by
    ext n
    simp only [Finset.mem_filter, Q, mem_nw, ge_iff_le, hA]
    omega
  have hR_card :
      R.card =
        (P.filter (fun n => 0 ≤ β⁻¹ n)).card
          + (A.filter (fun n => α n < 0)).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := R) (p := fun n => 0 ≤ n)
    simpa only [hR_pos, hR_neg] using hsplit.symm
  have hS_card :
      S.card =
        (B.filter (fun n => 0 ≤ α n)).card
          + (Q.filter (fun n => β⁻¹ n < 0)).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (p := fun n => 0 ≤ n)
    simpa only [hS_pos, hS_neg] using hsplit.symm
  have hP_card :
      P.card =
        (P.filter (fun n => 0 ≤ β⁻¹ n)).card
          + (B.filter (fun n => α n < 0)).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P) (p := fun n => 0 ≤ β⁻¹ n)
    simpa only [hP_cross] using hsplit.symm
  have hQ_card :
      Q.card =
        (A.filter (fun n => ¬ α n < 0)).card
          + (Q.filter (fun n => β⁻¹ n < 0)).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Q) (p := fun n => 0 ≤ β⁻¹ n)
    simp_all
  have hA_card :
      A.card =
        (A.filter (fun n => α n < 0)).card
          + (A.filter (fun n => ¬ α n < 0)).card := by
    exact (Finset.card_filter_add_card_filter_not
      (s := A) (p := fun n => α n < 0)).symm
  have hB_card :
      B.card =
        (B.filter (fun n => α n < 0)).card
          + (B.filter (fun n => 0 ≤ α n)).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := B) (p := fun n => α n < 0)
    simp_all
  have hse_image :
      (β.seFinset 0 0).card = A.card :=
    (Finset.card_image_of_injective _ β.injective).symm
  have hnw_image :
      (β.nwFinset 0 0).card = B.card :=
    (Finset.card_image_of_injective _ β.injective).symm
  have hmul_se_image :
      ((α * β).seFinset 0 0).card = R.card :=
    (Finset.card_image_of_injective _ β.injective).symm
  have hmul_nw_image :
      ((α * β).nwFinset 0 0).card = S.card :=
    (Finset.card_image_of_injective _ β.injective).symm
  have hcards :
      (R.card : ℤ) - S.card =
        ((P.card : ℤ) - Q.card) + ((A.card : ℤ) - B.card) := by
    omega
  rw [chi_eq_card, chi_eq_card, chi_eq_card,
    hmul_se_image, hmul_nw_image, hse_image, hnw_image]
  exact hcards

lemma b_step_one_iff (a b : ℤ) : τ.s a (b+1) = τ.s a b - 1 ↔ τ b < a := by
  rw [b_step τ a b]
  simp_all

lemma b_step_lt_iff (a b : ℤ) : τ.s a (b + 1) < τ.s a b ↔ τ b < a := by
  -- Proof written by GPT-5.
  have hiff := τ.b_step_one_iff a b
  have hstep : τ.s a (b + 1) ≤ τ.s a b ∧ τ.s a b ≤ τ.s a (b + 1) + 1 :=
    τ.s.b_step a b
  constructor
  · intro h
    exact hiff.mp (by omega)
  · intro h
    simp_all

lemma b_step_eq_iff (a b : ℤ) : τ.s a (b+1) = τ.s a b ↔ a ≤ τ b := by
  rw [b_step τ a b]
  simp_all

lemma b_step_ge_iff (a b : ℤ) : τ.s a (b + 1) ≥ τ.s a b ↔ a ≤ τ b := by
  constructor
  · intro h
    apply (τ.b_step_eq_iff a b).mp <| le_antisymm _ h
    rw [τ.b_step a b]
    omega
  · intro h
    apply le_of_eq
    rw [(τ.b_step_eq_iff a b).mpr h]

lemma a_step_one_iff (a b : ℤ) : τ.s (a+1) b = τ.s a b + 1 ↔ τ⁻¹ a ≥ b := by
  rw [a_step τ a b]
  by_cases h_ge : τ⁻¹ a ≥ b <;> simp [h_ge]

lemma a_step_gt_iff (a b : ℤ) : τ.s a b < τ.s (a + 1) b ↔ b ≤ τ⁻¹ a := by
  -- Proof written by GPT-5.
  have hiff := τ.a_step_one_iff a b
  have hstep : τ.s a b ≤ τ.s (a + 1) b ∧ τ.s (a + 1) b ≤ τ.s a b + 1 :=
    τ.s.a_step a b
  constructor
  · intro h
    exact hiff.mp (by omega)
  · intro h
    simp_all

lemma a_step_le_iff (a b : ℤ) : τ.s (a+1) b ≤ τ.s a b ↔ τ⁻¹ a < b := by
  constructor
  · intro h
    contrapose! h
    rwa [a_step_gt_iff]
  · intro h
    contrapose! h
    rwa [← a_step_gt_iff]

lemma a_step_one_iff' (u b : ℤ) : τ.s (τ u + 1) b = τ.s (τ u) b + 1 ↔ u ≥ b := by
  have := a_step_one_iff τ (τ u) b
  simpa [τ.mul_inv_cancel_eval] using this

lemma a_step_eq_iff (a b : ℤ) : τ.s (a+1) b = τ.s a b ↔ τ⁻¹ a < b := by
  rw [a_step τ a b]
  simp_all

lemma a_step_eq_iff' (u b : ℤ) : τ.s (τ u + 1) b = τ.s (τ u) b ↔ u < b := by
  have := a_step_eq_iff τ (τ u) b
  simpa [τ.mul_inv_cancel_eval] using this

/-- The set of inversion sources ending at `v`. -/
def inset (v : ℤ) : Set ℤ := {u | ⟨u, v⟩ ∈ invSet τ}

lemma inset_eq_nw (v : ℤ) : τ.inset v = northwestSet τ (τ v) v := by
  ext u
  constructor
  · intro uv_inv
    obtain ⟨u_lt_v, τv_lt_τu⟩ := uv_inv
    exact ⟨u_lt_v, le_of_lt τv_lt_τu⟩
  · intro uv_se
    obtain ⟨u_lt_v, τv_le_τu⟩ := uv_se
    exact (τ.inv_iff_le u_lt_v).mpr τv_le_τu

lemma invset_iff_inset (u v : ℤ) : ⟨u, v⟩ ∈ invSet τ ↔ u ∈ τ.inset v := by
  simp only [inset_eq_nw, northwestSet, Set.mem_ofPred_eq]
  constructor
  · intro ⟨u_lt, τ_le⟩
    exact ⟨u_lt, le_of_lt τ_le⟩
  · intro ⟨x_lt_n, σx_le_σn⟩
    exact (inv_iff_le τ x_lt_n).mpr σx_le_σn

lemma inset_finite (v : ℤ) : (τ.inset v).Finite := by
  rw [τ.inset_eq_nw v]
  apply τ.nw_finite

/-- The set of inversion targets starting at `u`. -/
def outset (u : ℤ) : Set ℤ := {v | ⟨u, v⟩ ∈ invSet τ}

lemma outset_eq_se (u : ℤ) : τ.outset u = southeastSet τ (τ u) u := by
  ext v
  constructor
  · intro uv_inv
    obtain ⟨u_lt_v, τv_lt_τu⟩ := uv_inv
    exact ⟨le_of_lt u_lt_v, τv_lt_τu⟩
  · intro uv_se
    obtain ⟨u_le_v, τv_lt_τu⟩ := uv_se
    exact (τ.inv_iff_lt u_le_v).mpr τv_lt_τu

lemma invset_iff_outset (u v : ℤ) : ⟨u, v⟩ ∈ invSet τ ↔ v ∈ τ.outset u := by
  simp only [outset_eq_se, southeastSet, Set.mem_ofPred_eq]
  constructor
  · intro ⟨u_lt, τ_le⟩
    exact ⟨le_of_lt u_lt, τ_le⟩
  · intro ⟨x_le_n, σx_lt_σn⟩
    exact (inv_iff_lt τ x_le_n).mpr σx_lt_σn

lemma outset_finite (u : ℤ) : (τ.outset u).Finite := by
  rw [τ.outset_eq_se u]
  apply τ.se_finite

/-- Reconstruct `τ n` from its shift and inversion set:
$\tau(n) = n - \chi_\tau$
$+ \#\{v \in \mathbb{Z} : (n,v) \in \operatorname{Inv} \tau\}$
$- \#\{u \in \mathbb{Z} : (u,n) \in \operatorname{Inv} \tau\}$.

*Proposition 2.11 (`prop:reconstruction`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
theorem reconstruction : ∀ n : ℤ,
  τ n = n - τ.χ + (τ.outset n).ncard - (τ.inset n).ncard := by
  intro n
  rw [← show τ.s (τ n) n = (τ.outset n).ncard by
    rw [s_eq_ncard, τ.outset_eq_se]]
  rw [← show (τ⁻¹).s n (τ n) = (τ.inset n).ncard by
    rw [s'_eq_ncard, τ.inset_eq_nw]]
  have := τ.duality (τ n) n
  omega

/-- Two ASP permutations are equal if they have the same inversion set and the
same shift. *Proposition 2.11 (`prop:reconstruction`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), consequence, part 2/2.* -/
theorem eq_of_inv_set_eq_of_chi_eq (σ τ : AspPerm)
    (h_inv : invSet σ = invSet τ) (h_χ : σ.χ = τ.χ) : σ = τ := by
  apply AspPerm.ext.mpr
  ext n
  rw [reconstruction σ n, reconstruction τ n, h_χ]
  suffices σ.outset n = τ.outset n ∧ σ.inset n = τ.inset n by
    simp only [this]
  constructor
  · ext v
    simp only [← invset_iff_outset]
    rw [h_inv]
  · ext v
    simp only [← invset_iff_inset]
    rw [h_inv]

/-- An ASP permutation with empty inversion set and zero shift is the identity. -/
theorem eq_id_of_inv_set_eq_empty_of_chi_eq_zero (τ : AspPerm)
    (h_inv : invSet τ = ∅) (h_χ : τ.χ = 0) : τ = AspPerm.id := by
  apply AspPerm.ext.mpr
  ext n
  rw [reconstruction τ n, h_χ]
  have h_out : τ.outset n = ∅ := by
    ext v
    simp only [outset, h_inv, Set.mem_empty_iff_false, Set.ofPred_false]
  have h_in : τ.inset n = ∅ := by
    ext v
    simp only [inset, h_inv, Set.mem_empty_iff_false, Set.ofPred_false]
  simp only [sub_zero, h_out, Set.ncard_empty, Nat.cast_zero, add_zero, h_in, id, id_eq]

@[simp]
lemma inv_set_id : invSet AspPerm.id = ∅ := by
  ext ⟨u, v⟩
  simp only [invSet, id, id_eq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
    not_lt]
  intro u_lt_v
  exact le_of_lt u_lt_v

@[simp] lemma s_chi_eq : τ.s.χ = τ.χ := rfl

lemma s_dual : τ.s.dual = (τ⁻¹).s := by
  apply (SF_ext τ.s.dual τ⁻¹.s).mpr
  intro a b
  rw [τ.s'_eq, ← τ.s_chi_eq]
  have := τ.s.duality b a
  omega

/-- The northwest count `(τ⁻¹).s b a` (the slipface dual value) equals the
cardinality of the northwest set. The slipface replacement for `s'_eq_nw_card`. -/
lemma s_dual_eq_nw_card (b a : ℤ) : (τ⁻¹).s b a = (τ.nwFinset a b).card := by
  rw [s'_eq_ncard]
  unfold nwFinset
  rw [Set.ncard_eq_toFinset_card _ (τ.nw_finite a b)]

/-- The bend set is a finite set on which the minimum defining the Demazure product is always
obtained. It is characterized in
*Lemma 3.13 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/5.* -/
lemma bend_set_sf (β : AspPerm) (b : ℤ) :
    SlipFace.bendSet β.s b = {l : ℤ | β⁻¹ (l - 1) < b ∧ b ≤ β⁻¹ l} := by
  -- Proof written by GPT 5.5.
  ext l
  simp only [SlipFace.bendSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hflat, hne⟩
    constructor
    · have hflat' : β.s ((l - 1) + 1) b = β.s (l - 1) b := by
        simpa only [sub_add_cancel] using hflat.symm
      exact (β.a_step_eq_iff (l - 1) b).mp hflat'
    · have hnot : ¬ β⁻¹ l < b := by
        intro hlt
        have hflat' : β.s (l + 1) b = β.s l b :=
          (β.a_step_eq_iff l b).mpr hlt
        exact hne hflat'.symm
      exact not_lt.mp hnot
  · rintro ⟨hleft, hright⟩
    constructor
    · have hflat : β.s ((l - 1) + 1) b = β.s (l - 1) b :=
        (β.a_step_eq_iff (l - 1) b).mpr hleft
      simpa only [sub_add_cancel] using hflat.symm
    · intro hsame
      have hlt : β⁻¹ l < b :=
        (β.a_step_eq_iff l b).mp hsame.symm
      exact not_lt_of_ge hright hlt

/-- Formula (14) (`eq:Deltasa`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227),
characterizing the values of a permutation via the second iterated difference of its slipface. -/
lemma Delta_eq (a b : ℤ) : τ.s.Δ a b = if τ b = a then 1 else 0 := by
  let d1 := τ.s (a+1) b - τ.s (a+1) (b+1)
  let d2 := τ.s a b - τ.s a (b+1)
  suffices d1 - d2 = if τ b = a then 1 else 0 by
    unfold SlipFace.Δ
    omega
  have h1 : d1 = if τ b ≤ a then 1 else 0 := by
    unfold d1; rw [τ.b_step (a+1) b]
    omega
  have h2 : d2 = if τ b < a then 1 else 0 := by
    unfold d2; rw [τ.b_step a b]
    omega
  rw [h1, h2]
  by_cases h : τ b < a
  · have h' : τ b ≤ a := le_of_lt h
    have h'' : τ b ≠ a := ne_of_lt h
    simp only [h', ↓reduceIte, h, sub_self, h'']
  simp only [h, ↓reduceIte, sub_zero]
  by_cases h' : τ b = a
  · simp only [h', le_refl, ↓reduceIte]
  have h' : ¬ (τ b ≤ a) := by
    contrapose! h'
    push Not at h
    exact le_antisymm h' h
  simpa [h, h']

lemma Γ_eq : τ.s.Γ = { ⟨a, b⟩ | τ b = a } := by
  ext ⟨a, b⟩
  simp only [SlipFace.Γ, τ.Delta_eq, ite_eq_left_iff, zero_ne_one, imp_false,
    Decidable.not_not, Set.mem_ofPred_eq]

/-- The slipface of an ASP permutation is submodular.
*Proposition 4.3* (`prop:imageASP`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227), one direction. -/
lemma submodular : τ.s.submodular := by
  intro a b
  have Delta_eq := τ.Delta_eq a b
  by_cases h : τ b = a <;> simp [h, Delta_eq]

/-! ### Ramps, lamps, and wing parameters

This section defines the ramp and lamp regions associated to an ASP
permutation. These are Young diagrams associated to particular values of `a` or `b`,
useful in characterizing Demazure factorizations of 321-avoiding permutations.

This material is not present in [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/

section RampWings
variable (τ : AspPerm)

/-- The `b`-ramp of an ASP permutation: the region, shaped like a Young diagram, of pairs `(m,n)`
such that $s_\tau(\ell,b) \ge m$ and $s^∨_\tau(b,\ell) \ge n$ for some $\ell$. -/
def ramp (b : ℤ) : Set (ℤ × ℤ) :=
  {⟨m, n⟩ | ∃ l : ℤ, τ.s l b ≥ m ∧ τ⁻¹.s b l ≥ n}

/-- The `a`-lamp of an ASP permutation, defined as the dual of a ramp. -/
def lamp (a : ℤ) : Set (ℤ × ℤ) :=
  {⟨m, n⟩ | ∃ l : ℤ, τ.s a l ≥ m ∧ τ⁻¹.s l a ≥ n}

lemma ramp_closed (b : ℤ) {m₁ n₁ m₂ n₂ : ℤ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) :
  ⟨m₂, n₂⟩ ∈ τ.ramp b → ⟨m₁, n₁⟩ ∈ τ.ramp b := by
  intro h
  rcases h with ⟨l, hlm, hln⟩
  use l
  constructor <;> omega


lemma ramp_lamp_dual (b m n : ℤ) :
  ⟨m,n⟩ ∈ τ.ramp b ↔ ⟨n, m⟩ ∈ (τ⁻¹).lamp b := by
  unfold ramp lamp
  rw [inv_inv τ]
  constructor <;> (intro h; rcases h with ⟨l, _, _⟩; use l)

lemma mem_ramp_iff_s_ge (b m n : ℤ) :
  ⟨m, n⟩ ∈ τ.ramp b ↔ τ.s (b + m - n - τ.χ) b ≥ m := by
  constructor
  · intro mn_ramp
    rcases mn_ramp with ⟨l, hm, hn⟩
    by_cases hl : l ≤ b + m - n - τ.χ
    · have := a_move_up τ l (b + m - n - τ.χ) b hl
      omega
    · have ineq := b_move_up τ⁻¹ b (b + m - n - τ.χ) l (by omega)
      rw [τ.s_eq (b + m - n - τ.χ) b]
      omega
  · intro s_ge
    use b + m - n - τ.χ
    constructor
    · exact s_ge
    · rw [s_eq] at s_ge
      omega

lemma mem_lamp_iff_s_ge (a m n : ℤ) :
  ⟨m, n⟩ ∈ τ.lamp a ↔ τ⁻¹.s (a - m + n + τ.χ) a ≥ n := by
  have := ramp_lamp_dual (τ := τ⁻¹) a n m
  rw [inv_inv] at this
  rw [← this]
  rw [mem_ramp_iff_s_ge, chi_dual]
  constructor <;> (intro h; convert h using 2; omega)

namespace Wings
variable (b m n : ℤ) (m_pos : m > 0) (n_pos : n > 0)

private def R : Set ℤ := {n : ℤ | τ.s n b < m}

private lemma R_nonempty (m_pos : m > 0) : (R τ b m).Nonempty := by
  have := tend_zero_a (τ := τ) b
  obtain ⟨n, hn⟩ := this
  use n
  unfold R; simp_all

private lemma R_bddAbove : ∃ N : ℤ, ∀ n ∈ R τ b m, n ≤ N := by
  use m + b - τ.χ
  intro n hn
  simp only [R] at hn
  have := lt_of_le_of_lt (τ.s_ge n b) hn
  omega

private def L : Set ℤ := {a : ℤ | τ⁻¹.s b a ≥ n}

private lemma L_nonnempty : (L τ b n).Nonempty := by
  use b - n - τ.χ
  unfold L; simp only [ge_iff_le, Set.mem_ofPred_eq]
  refine le_trans ?_ (τ⁻¹.s_ge b (b - n - τ.χ))
  rw [τ.chi_dual]
  omega

private lemma L_bddAbove (n_pos : n > 0) : ∃ A : ℤ, ∀ a ∈ L τ b n, A ≥ a := by
  have := tend_zero_b (τ := τ⁻¹) b
  obtain ⟨a, ha⟩ := this
  use a
  intro a' a'_L
  unfold L at a'_L; simp only [ge_iff_le, Set.mem_ofPred_eq] at a'_L
  contrapose! a'_L with a_lt_a'
  have := (τ⁻¹.s_noninc b (le_of_lt a_lt_a')).1
  omega

end Wings

/-- The rightmost index whose image is the last value with `s` below `m` in row `b`. -/
noncomputable def v (b : ℤ) {m : ℤ} (m_pos : m > 0) : ℤ :=
  τ⁻¹ ( Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.R_bddAbove τ b m) (Wings.R_nonempty τ b m m_pos) )

private lemma v_spec (b : ℤ) {m : ℤ} (m_pos : m > 0) :
  τ.s (τ (τ.v b m_pos)) b < m
  ∧ ∀ a : ℤ, τ.s a b < m → a ≤ τ (τ.v b m_pos) := by
  let v := τ.v b m_pos
  let τv := Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.R_bddAbove τ b m) (Wings.R_nonempty τ b m m_pos)
  have τ_vs: τ v = τv := by simp only [AspPerm.v, mul_inv_cancel_eval, v, τv]
  let R := Wings.R τ b m
  have : τv ∈ R ∧ ∀ n : ℤ, n ∈ R → n ≤ τv := Classical.choose_spec
    (Int.exists_greatest_of_bdd (Wings.R_bddAbove τ b m) (Wings.R_nonempty τ b m m_pos))
  rw [← τ_vs] at this
  simpa [v, R, Wings.R] using this

lemma v_crit (b : ℤ) {m : ℤ} (m_pos : m > 0) (v : ℤ) :
  v = τ.v b m_pos ↔ τ.s (τ v) b = m - 1 ∧ b ≤ v := by
  constructor
  · intro v_eq
    have v_spec : τ.s (τ v) b < m ∧ ∀ a : ℤ, τ.s a b < m → a ≤ τ v := by
      subst v; exact τ.v_spec b m_pos
    obtain ⟨s_lt_m, τv_max⟩ := v_spec
    have s_next : τ.s (τ v + 1) b ≥ m := by
      by_contra! s_next_lt
      have a_le : τ v + 1 ≤ τ v := τv_max (τ v + 1) s_next_lt
      omega
    have s_inc : τ.s (τ v) b < τ.s (τ v + 1) b := lt_of_lt_of_le s_lt_m s_next
    have v_ge_b : b ≤ v := by
      by_contra! v_lt_b
      have : τ.s (τ v + 1) b = τ.s (τ v) b := (a_step_eq_iff' τ v b).mpr v_lt_b
      simp_all
    let s_inc : τ.s (τ v + 1) b = τ.s (τ v) b + 1 := (a_step_one_iff' τ v b).mpr v_ge_b
    have s_next_le : τ.s (τ v + 1) b ≤ m := by
      rw [s_inc]
      apply Int.lt_iff_add_one_le.mpr
      linarith [v_eq]
    have : τ.s (τ v + 1) b = m := le_antisymm s_next_le s_next
    rw [s_inc] at this
    exact ⟨by linarith [this, s_inc], v_ge_b⟩
  · rintro ⟨s_eq, v_ge_b⟩
    let v₀ := τ.v b m_pos
    have τv_le : τ v ≤ τ v₀ := by
      apply (τ.v_spec b m_pos).2 (τ v)
      linarith [s_eq]
    have τv_ge : τ v₀ ≤ τ v := by
      by_contra! τv_lt
      have τv_le : τ v + 1 ≤ τ (τ.v b m_pos) := by linarith [τv_le]
      have : (τ.s (τ v + 1) b ≤ τ.s (τ v₀) b) := (τ.s_nondec τv_le b).1
      have : (τ.s (τ v) b) + 1 ≤ τ.s (τ v₀) b := by
        rwa [(a_step_one_iff' τ v b).mpr v_ge_b] at this
      linarith [this, s_eq, (τ.v_spec b m_pos).1]
    exact τ.injective <| le_antisymm τv_le τv_ge

lemma s_τv_b (b : ℤ) {m : ℤ} (m_pos : m > 0) :
  τ.s (τ (τ.v b m_pos)) b = m - 1 := by
  exact ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).1

lemma v_ge (b : ℤ) {m : ℤ} (m_pos : m > 0) : b ≤ τ.v b m_pos :=
  ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).2

lemma τv_lt (b : ℤ) {m : ℤ} (m_pos : m > 0)
  {a : ℤ} (s_ge_m : m ≤ τ.s a b) : τ (τ.v b m_pos) < a := by
  by_contra! τv_ge_a
  have h := (τ.s_nondec τv_ge_a b).1
  have := ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).1
  rw [this] at h
  have : m ≤ m-1 := le_trans s_ge_m h
  linarith [this]

/-- The rightmost index witnessing the dual lower bound `n` in row `b`. -/
noncomputable def u (b : ℤ) {n : ℤ} (n_pos : n > 0) : ℤ :=
  τ⁻¹ <|Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.L_bddAbove τ b n n_pos) (Wings.L_nonnempty τ b n)

private lemma u_spec (b : ℤ) {n : ℤ} (n_pos : n > 0) :
  τ⁻¹.s b (τ (τ.u b n_pos)) ≥ n
  ∧ ∀ a : ℤ, τ⁻¹.s b a ≥ n → a ≤ τ (τ.u b n_pos) := by
  let u := τ.u b n_pos
  let τu := Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.L_bddAbove τ b n n_pos) (Wings.L_nonnempty τ b n)
  have τ_us: τ u = τu := by simp only [AspPerm.u, mul_inv_cancel_eval, u, τu]
  let L := Wings.L τ b n
  have : τu ∈ L ∧ ∀ n : ℤ, n ∈ L → τu ≥ n := Classical.choose_spec
    (Int.exists_greatest_of_bdd (Wings.L_bddAbove τ b n n_pos) (Wings.L_nonnempty τ b n))
  rw [← τ_us] at this
  simpa [L, Wings.L] using this

lemma u_crit (b : ℤ) {n : ℤ} (n_pos : n > 0) (u : ℤ) :
  u = τ.u b n_pos ↔ τ⁻¹.s b (τ u) = n ∧ u < b := by
  constructor
  · intro u_eq
    have u_spec : τ⁻¹.s b (τ u) ≥ n ∧ ∀ a : ℤ, τ⁻¹.s b a ≥ n → a ≤ τ u := by
      subst u; exact τ.u_spec b n_pos
    obtain ⟨s_ge_n, τu_max⟩ := u_spec
    have s_next : τ⁻¹.s b (τ u + 1) < n := by
      by_contra! s_next_ge
      have a_le : τ u + 1 ≤ τ u := τu_max (τ u + 1) s_next_ge
      omega
    have s_ge_n_inv : (τ⁻¹).s b (τ u) ≥ n := by
      simpa using s_ge_n
    have s_next_inv : (τ⁻¹).s b (τ u + 1) < n := by
      simpa using s_next
    have u_lt_b : u < b := by
      by_contra! u_ge_b
      rw [show (τ⁻¹).s b (τ u + 1) = (τ⁻¹).s b (τ u) by
        apply ((τ⁻¹).b_step_eq_iff b (τ u)).2
        simpa using u_ge_b] at s_next_inv
      exact lt_irrefl _ (lt_of_lt_of_le s_next_inv s_ge_n_inv)
    have hs_dec : (τ⁻¹).s b (τ u + 1) = (τ⁻¹).s b (τ u) - 1 := by
      apply ((τ⁻¹).b_step_one_iff b (τ u)).2
      simpa using u_lt_b
    have hs_eq_n : (τ⁻¹).s b (τ u) = n := by
      rw [hs_dec] at s_next_inv
      omega
    exact ⟨by simpa using hs_eq_n, u_lt_b⟩
  · rintro ⟨s_eq, u_lt_b⟩
    let u₀ := τ.u b n_pos
    have τu_le : τ u ≤ τ u₀ := by
      apply (τ.u_spec b n_pos).2 (τ u)
      rw [s_eq]
    have τu_ge : τ u₀ ≤ τ u := by
      by_contra! τu_lt
      have τu_succ_le : τ u + 1 ≤ τ u₀ := by omega
      have hs_noninc : (τ⁻¹).s b (τ u₀) ≤ (τ⁻¹).s b (τ u + 1) := by
        exact ((τ⁻¹).s_noninc (a := b) τu_succ_le).1
      have hs_dec : (τ⁻¹).s b (τ u + 1) = (τ⁻¹).s b (τ u) - 1 := by
        apply ((τ⁻¹).b_step_one_iff b (τ u)).2
        simpa using u_lt_b
      have hs_u0_ge_n : (τ⁻¹).s b (τ u₀) ≥ n := by
        simpa [u₀] using (τ.u_spec b n_pos).1
      have hs_u0_le : (τ⁻¹).s b (τ u₀) ≤ n - 1 := by
        simp_all
      omega
    exact τ.injective <| le_antisymm τu_le τu_ge

lemma s'_b_τu (b : ℤ) {n : ℤ} (n_pos : n > 0) :
  τ⁻¹.s b (τ (τ.u b n_pos)) = n := by
  exact ((τ.u_crit b n_pos (τ.u b n_pos)).mp rfl).1

lemma s'_pos_of_lt {u b : ℤ} (u_lt_b : u < b) : τ⁻¹.s b (τ u) ≥ 1 := by
  have h_pos : 0 < (τ.nwFinset (τ u) b).card := by
    apply Finset.card_pos.mpr
    exact ⟨u, (τ.mem_nw (τ u) b u).mpr ⟨u_lt_b, le_rfl⟩⟩
  rw [τ.s_dual_eq_nw_card]
  exact_mod_cast h_pos

lemma u_lt (b : ℤ) {n : ℤ} (n_pos : n > 0) : τ.u b n_pos < b :=
  ((τ.u_crit b n_pos (τ.u b n_pos)).mp rfl).2

lemma τu_ge (b : ℤ) {n : ℤ} (n_pos : n > 0)
  {a : ℤ} (s_ge_n : n ≤ τ⁻¹.s b a) : τ (τ.u b n_pos) ≥ a := by
  by_contra! τu_lt_a
  have hu_ge : a ≤ τ (τ.u b n_pos) := (τ.u_spec b n_pos).2 a s_ge_n
  omega

/-- A box lies in the ramp exactly when a specific inversion belongs to `invSet τ`,
given by the functions `u` and `v` above. -/
theorem inv_ramp_correspondence (b : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨m, n⟩ ∈ τ.ramp b ↔ ⟨τ.u b n_pos, τ.v b m_pos⟩ ∈ invSet τ := by
  let u := τ.u b n_pos
  let v := τ.v b m_pos
  have u_lt_b : u < b := τ.u_lt b n_pos
  have v_gt_b : b ≤ v := τ.v_ge b m_pos
  have inv_simp : ⟨u, v⟩ ∈ invSet τ ↔ τ v < τ u := by
    simp only [invSet, Set.mem_ofPred_eq, lt_of_lt_of_le u_lt_b v_gt_b, true_and]
  suffices ⟨m, n⟩ ∈ τ.ramp b ↔ τ v < τ u by
    rw [this, inv_simp]
  let a := b + m - n - τ.χ
  constructor
  · intro mn_ramp
    have s_ge_m : τ.s a b ≥ m := (mem_ramp_iff_s_ge (τ := τ) b m n).mp mn_ramp
    have s'_ge_n : τ⁻¹.s b a ≥ n := by
      have := τ.duality a b
      omega
    have a_gt_v : a > τ v := by
      contrapose! s_ge_m with a_le_v
      have h_lt : τ.s (τ v) b < m := (τ.v_spec b m_pos).1
      have h_le : τ.s a b ≤ τ.s (τ (τ.v b m_pos)) b := (τ.s_nondec a_le_v b).1
      exact lt_of_le_of_lt h_le h_lt
    have a_le_u : a ≤ τ u := by
      exact (τ.u_spec b n_pos).2 a s'_ge_n
    exact lt_of_lt_of_le a_gt_v a_le_u
  · intro τ_v_lt_u
    use τ u
    constructor
    · have u_spec := (τ.v_spec b m_pos).2 (τ u)
      contrapose! τ_v_lt_u with h
      exact u_spec h
    · exact (τ.u_spec b n_pos).1

end RampWings

/-! ### Reduced products and weak orders

This section introduces some infrastructure about inversion sets. -/

/-- A product $\alpha \beta$ is reduced if
$\operatorname{Inv}(\alpha) \cap \operatorname{Inv}(\beta^{-1})$ is empty.

*Definition 2.7 (`defn:reducedProduct`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def ReducedProduct (α β : AspPerm) : Prop :=
  Disjoint (invSet α) (invSet (β⁻¹).func)

/-- The left weak order: `σ ≤L τ` if and only if $\operatorname{Inv} \sigma \subseteq
\operatorname{Inv} \tau$. *Definition 2.6 (`defn:weakOrders`), part 1/2, of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def leWeakL (σ τ : AspPerm) : Prop := invSet σ ⊆ invSet τ
/-- Infix notation for the left weak order on ASP permutations. -/
infix:50 " ≤L " => leWeakL

/-- The right weak order: `σ ≤R τ` if and only if
$\operatorname{Inv}(\sigma^{-1}) \subseteq \operatorname{Inv}(\tau^{-1})$.
*Definition 2.6 (`defn:weakOrders`), part 2/2, of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def leWeakR (σ τ : AspPerm) : Prop := invSet (σ⁻¹).func ⊆ invSet (τ⁻¹).func
/-- Infix notation for the right weak order on ASP permutations. -/
infix:50 " ≤R " => leWeakR

lemma le_weak_L_of_R {σ τ : AspPerm} (h_R : σ ≤R τ) : σ⁻¹ ≤L τ⁻¹ := h_R

lemma le_weak_R_of_L {σ τ : AspPerm} (h_L : σ ≤L τ) : σ⁻¹ ≤R τ⁻¹ := by
  intro x; simp only [inv_inv]; intro hx
  exact h_L hx

/-- A product `α β` is reduced exactly when `α` is below `α β` in right
weak order. *Lemma 2.8 (`lem:reducedWeakEquivs`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
lemma reduced_iff_leR (α β : AspPerm) :
    ReducedProduct α β ↔ α ≤R α * β := by
  -- Proof written by Codex.
  constructor
  · intro hred
    rintro ⟨p, q⟩ hpq
    obtain ⟨p_lt_q, hαpq⟩ := hpq
    refine ⟨p_lt_q, ?_⟩
    have hnot : ¬ β⁻¹ (α⁻¹ p) < β⁻¹ (α⁻¹ q) := by
      intro hβ
      have hα : ⟨α⁻¹ q, α⁻¹ p⟩ ∈ invSet α := by
        refine ⟨hαpq, ?_⟩
        simp_all
      have hβ' : ⟨α⁻¹ q, α⁻¹ p⟩ ∈ invSet (β⁻¹).func :=
        ⟨hαpq, hβ⟩
      exact Set.disjoint_left.mp hred hα hβ'
    have hne : β⁻¹ (α⁻¹ q) ≠ β⁻¹ (α⁻¹ p) := by
      intro h
      apply (β⁻¹).injective at h
      omega
    change (α * β)⁻¹ q < (α * β)⁻¹ p
    rw [mul_inv_rev]
    change β⁻¹ (α⁻¹ q) < β⁻¹ (α⁻¹ p)
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  · intro hweak
    apply Set.disjoint_left.mpr
    rintro ⟨u, v⟩ huv hβ
    have hαinv : ⟨α v, α u⟩ ∈ invSet (α⁻¹).func :=
      (α.inv_set_inverse u v).mp huv
    have hmul := hweak hαinv
    obtain ⟨-, hmul⟩ := hmul
    change (α * β)⁻¹ (α u) < (α * β)⁻¹ (α v) at hmul
    rw [mul_inv_rev] at hmul
    change β⁻¹ (α⁻¹ (α u)) < β⁻¹ (α⁻¹ (α v)) at hmul
    simp only [inv_mul_cancel_eval] at hmul
    exact (not_lt_of_ge (le_of_lt hβ.2)) hmul

/-- A product `α β` is reduced exactly when `β` is below `α β` in left
weak order. *Lemma 2.8 (`lem:reducedWeakEquivs`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
lemma reduced_iff_leL (α β : AspPerm) :
    ReducedProduct α β ↔ β ≤L α * β := by
  -- Proof written by Codex.
  constructor
  · intro hred
    rintro ⟨p, q⟩ hpq
    obtain ⟨p_lt_q, hβpq⟩ := hpq
    refine ⟨p_lt_q, ?_⟩
    have hnot : ¬ α (β p) < α (β q) := by
      intro hα
      have hα' : ⟨β q, β p⟩ ∈ invSet α := ⟨hβpq, hα⟩
      have hβ' : ⟨β q, β p⟩ ∈ invSet (β⁻¹).func := by
        refine ⟨hβpq, ?_⟩
        simp_all
      exact Set.disjoint_left.mp hred hα' hβ'
    have hne : α (β q) ≠ α (β p) := by
      intro h
      apply α.injective at h
      omega
    change α (β q) < α (β p)
    exact lt_of_le_of_ne (le_of_not_gt hnot) hne
  · intro hweak
    apply Set.disjoint_left.mpr
    rintro ⟨u, v⟩ huv hβ
    have hβinv : ⟨β⁻¹ v, β⁻¹ u⟩ ∈ invSet β := by
      refine ⟨hβ.2, ?_⟩
      simp only [mul_inv_cancel_eval]
      exact huv.1
    have hmul := hweak hβinv
    obtain ⟨-, hmul⟩ := hmul
    change α (β (β⁻¹ u)) < α (β (β⁻¹ v)) at hmul
    simp only [mul_inv_cancel_eval] at hmul
    exact (not_lt_of_ge (le_of_lt huv.2)) hmul

/-- Inversion reverses the factors in a reduced product. -/
lemma reducedProduct_inv_swap (α β : AspPerm) :
    ReducedProduct α β ↔ ReducedProduct β⁻¹ α⁻¹ := by
  unfold ReducedProduct
  simp only [inv_inv]
  exact disjoint_comm

/-- Slide right inversions from `α` to boxes indexed by `τ`. -/
noncomputable def sr (τ α : AspPerm) : (ℤ × ℤ) → (ℤ × ℤ) := fun x =>
  ⟨τ⁻¹ (α x.1), τ⁻¹ (α x.2)⟩

lemma sr_crit (τ α : AspPerm) : ∀ (u v : ℤ),
  ⟨u, v⟩ ∈ (τ.sr α) '' invSet α ↔ ⟨τ v, τ u⟩ ∈ invSet α⁻¹.func := by
  intro u v
  constructor
  · intro h
    rcases h with ⟨⟨u, v⟩, uv_inv, xy_inv, rfl⟩
    simp only [τ.mul_inv_cancel_eval]
    exact (α.inv_set_inverse u v).mp uv_inv
  · intro h
    use ⟨α⁻¹ (τ u), α⁻¹ (τ v)⟩
    constructor
    · have := (α⁻¹.inv_set_inverse (τ v) (τ u)).mp h
      simpa
    · unfold sr
      simp

lemma sr_subset (τ α : AspPerm) (h_R : α ≤R τ) : (τ.sr α) '' invSet α ⊆ invSet τ := by
  intro x hx; obtain ⟨u, v⟩ := x
  apply (sr_crit τ α u v).mp at hx
  apply h_R at hx
  obtain ⟨τu_gt_τv, u_lt_v⟩ := hx
  simp only [inv_mul_cancel_eval] at u_lt_v
  exact ⟨u_lt_v, τu_gt_τv⟩

/-- The min-plus Demazure-product value is at least `n` at `(a, b)`. -/
def dprodValGe (α β : AspPerm) (a b n : ℤ) : Prop :=
  ∀ l : ℤ, α.s a l + β.s l b ≥ n

/-- Pointwise lower-bound predicate for a candidate Demazure product. -/
def leDprod (τ α β : AspPerm) : Prop :=
  ∀ a b : ℤ, dprodValGe α β a b (τ.s a b)

/-- The min-plus Demazure-product value is at most `n` at `(a, b)`. -/
def dprodValLe (α β : AspPerm) (a b n : ℤ) : Prop :=
  ∃ l : ℤ, α.s a l + β.s l b ≤ n

/-- Pointwise upper-bound predicate for a candidate Demazure product. -/
def geDprod (τ α β : AspPerm) : Prop :=
  ∀ a b : ℤ, dprodValLe α β a b (τ.s a b)

/-- Pointwise equality predicate for a candidate Demazure product. -/
def eqDprod (τ α β : AspPerm) : Prop :=
  τ.leDprod α β ∧ τ.geDprod α β

lemma chi_ge_of_dprod_ge {α β τ : AspPerm} (h_ge : τ.leDprod α β) :
  α.χ + β.χ ≥ τ.χ := by
  rcases α⁻¹.tend_zero_a 0 with ⟨l, hl⟩
  rcases β⁻¹.tend_zero_a l with ⟨c, hc⟩
  have eq := h_ge 0 c l
  rw [α.s_eq, β.s_eq] at eq
  linarith [τ.s_ge 0 c]

lemma chi_le_of_dprod_le {α β τ : AspPerm} (h_le : τ.geDprod α β) :
  α.χ + β.χ ≤ τ.χ := by
  rcases τ⁻¹.tend_zero_a 0 with ⟨c, hc⟩
  rcases h_le 0 c with ⟨l, hl⟩
  rw [τ.s_eq] at hl
  linarith [α.s_ge 0 l, β.s_ge l c]

lemma chi_eq_of_drop_eq {τ α β : AspPerm} (h_eq : τ.eqDprod α β) :
  α.χ + β.χ = τ.χ :=
  Int.le_antisymm (chi_le_of_dprod_le h_eq.2) (chi_ge_of_dprod_ge h_eq.1)

lemma dprod_inv_eq_inv_dprod (τ α β : AspPerm) (h_eq : τ.eqDprod α β) :
  τ⁻¹.eqDprod (β⁻¹) (α⁻¹) := by
  have hχ : α.χ + β.χ = τ.χ := chi_eq_of_drop_eq h_eq
  constructor
  · intro a b l
    have eqα : α⁻¹.s l b = l - b + α.s b l - α.χ := by have := α.s'_eq l b; omega
    have eqβ : β⁻¹.s a l = a - l + β.s l a - β.χ := by have := β.s'_eq a l; omega
    have eqτ : τ⁻¹.s a b = a - b + τ.s b a - τ.χ := by have := τ.s'_eq a b; omega
    rw [eqα, eqβ, eqτ, ← hχ]
    have := h_eq.1 b a l
    omega
  · intro a b
    rcases h_eq.2 b a with ⟨l, hl⟩
    use l
    have eqα : α⁻¹.s l b = l - b + α.s b l - α.χ := by have := α.s'_eq l b; omega
    have eqβ : β⁻¹.s a l = a - l + β.s l a - β.χ := by have := β.s'_eq a l; omega
    have eqτ : τ⁻¹.s a b = a - b + τ.s b a - τ.χ := by have := τ.s'_eq a b; omega
    rw [eqα, eqβ, eqτ, ← hχ]
    omega

/-- A characterization of Demazure products in terms of the Young diagrams called
"ramps" and "lamps" above. This is the key input in classifying the Demazure factorizations
of 321-avoiding permutations.

This theorem is not present in [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
theorem ramp_dprod_legos (α β : AspPerm) (a b M N : ℤ)
  (habMN : a - b + α.χ + β.χ = M - N) :
  dprodValGe α β a b M ↔
  ∀ m ∈ Set.Icc 1 M, ∀ n ∈ Set.Icc 1 N,
  ⟨m, n⟩ ∈ β.ramp b ∨ ⟨M+1-m, N+1-n⟩ ∈ α.lamp a
  := by
  constructor
  · intro dprod m m_icc n n_icc
    let m' := M + 1 - m
    let n' := N + 1 - n
    suffices ⟨m, n⟩ ∈ β.ramp b ∨ ⟨n', m'⟩ ∈ α⁻¹.ramp a by
      have h := ramp_lamp_dual α⁻¹ a (N+1-n) (M+1-m)
      rw [inv_inv] at h
      rw [← h]
      exact this
    have sα := mem_ramp_iff_s_ge α⁻¹ a n' m'
    have sβ := mem_ramp_iff_s_ge β b m n
    rw [sα, sβ]
    replace dprod : ∀ l, α.s a l + β.s l b ≥ M := dprod
    contrapose! dprod with ineqs
    let l := b + m - n  - β.χ
    use l
    rw [← show l = a + n' - m' - α⁻¹.χ by
      simp only [α.chi_dual, sub_neg_eq_add, l, n', m']
      linarith [habMN]] at ineqs
    obtain ⟨hβ, hα⟩ := ineqs
    have hβ : β.s l b ≤ m-1 := Int.le_sub_one_of_lt hβ
    have hα : α.s a l ≤ M  - m := by
      linarith [α.s_eq a l]
    have : α.s a l + β.s l b ≤ M-1 := by
      linarith [add_le_add (α.s_ge a l) hβ]
    exact Int.lt_of_le_sub_one this
  · intro hramp l
    contrapose! hramp with ineq
    obtain ineq : α.s a l + β.s l b ≤ M - 1 := Int.le_sub_one_of_lt ineq
    have ineq' : α⁻¹.s l a + β⁻¹.s b l ≤ N -1 := by
      linarith [α.s'_eq l a, β.s'_eq b l]
    let m := β.s l b + 1
    let n := β⁻¹.s b l + 1
    have l_eq : l = m - n + b - β.χ := by
      linarith [β.s_eq l b]
    have m_icc : m ∈ Set.Icc 1 M := by
      constructor
      · linarith [β.s_nonneg l b]
      · linarith [ineq, α.s_nonneg a l]
    have n_icc : n ∈ Set.Icc 1 N := by
      constructor
      · linarith [β⁻¹.s_nonneg b l]
      · linarith [ineq', α⁻¹.s_nonneg l a]
    use m, m_icc, n, n_icc
    constructor
    · show ⟨m, n⟩ ∉ β.ramp b
      intro h_mn
      apply (mem_ramp_iff_s_ge β b m n).mp at h_mn
      have hm : β.s l b ≥ m := by
        convert h_mn using 2
        linarith [l_eq]
      unfold m at hm
      linarith [hm]
    · show ⟨M+1-m, N+1-n⟩ ∉ α.lamp a
      intro h_mn
      have s_ge := (mem_lamp_iff_s_ge α a (M + 1 - m) (N + 1 - n)).mp h_mn
      have : (a - (M + 1 - m) + (N + 1 - n) + α.χ) = l := by
        linarith [N, l_eq]
      have : α⁻¹.s l a ≥ N + 1 - n := by
        rwa [this] at s_ge
      linarith [ineq']

/-!
  ## The essential set of a permutation

  This section formalizes results from Section 7.2 of
  [An extended Demazure product](https://arxiv.org/abs/2206.14227) about the essential set of a
  permutation and permutations of bounded difference.
  -/

/-- The essential set of an ASP permutation. -/
def ess (τ : AspPerm) : Set (ℤ × ℤ) :=
  {⟨a, b⟩ | τ b < a ∧ a ≤ τ (b-1) ∧ τ⁻¹ a < b ∧ b ≤ τ⁻¹ (a-1)}

lemma ess_asp_eq_ess_sf (τ : AspPerm) : τ.ess = τ.s.ess := by
  ext ⟨a, b⟩
  unfold AspPerm.ess SlipFace.ess
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rw [← b_step_lt_iff] at h1
    rw [← b_step_eq_iff, Int.sub_add_cancel] at h2
    rw [← a_step_eq_iff] at h3
    rw [← a_step_gt_iff, Int.sub_add_cancel] at h4
    exact ⟨h4, Eq.symm h3, h1, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    nth_rewrite 2 [← Int.sub_add_cancel a 1] at h1
    rw [a_step_gt_iff] at h1
    let h2 := Eq.symm h2
    rw [τ.a_step_eq_iff a b] at h2
    rw [b_step_lt_iff] at h3
    nth_rewrite 1 [← Int.sub_add_cancel b 1] at h4
    rw [b_step_eq_iff] at h4
    exact ⟨h3, h4, h2, h1⟩

/-- The bounded-difference condition for an ASP permutation. -/
def isBdiff : Prop := ∃ (M : ℤ), ∀ (n : ℤ), abs (n - τ n) ≤ M

private def width_bound (N : ℤ) : Prop :=
  ∀ (a b : ℤ), N ≤ abs (a - b) → τ.s a b = max 0 (a - b + τ.χ)


private lemma width_sides : (∃ (N : ℤ), τ.width_bound N) ↔ (∃ (M N : ℤ), ∀ (a b : ℤ),
  (a - b ≤ M → τ.s a b = 0) ∧ (a - b ≥ N → τ⁻¹.s b a = 0)) := by
  constructor
  · rintro ⟨N0, hN0⟩
    let N := max (abs N0) (abs τ.χ)
    have hN : τ.width_bound N := by
      intro a b hab
      exact hN0 a b <| (le_abs_self N0).trans <| (le_max_left _ _).trans hab
    have Npos : 0 ≤ N := (abs_nonneg N0).trans (le_max_left _ _)
    have Ngeχ : τ.χ ≤ N := (le_abs_self τ.χ).trans (le_max_right _ _)
    have Nge_negχ : -τ.χ ≤ N := (neg_le_abs τ.χ).trans (le_max_right _ _)
    use -N, N
    intro a b
    constructor <;> intro hab
    · rw [hN a b (by rw [abs_of_nonpos (by omega)]; omega), max_eq_left (by omega)]
    · rw [τ.s'_eq, hN a b (by rw [abs_of_nonneg (by omega)]; omega),
        max_eq_right (by omega)]
      omega
  · rintro ⟨M, N, hMN⟩
    use max |M| |N|
    intro a b hab
    specialize hMN a b
    rw [← τ.s_chi_eq, τ.s.eq_iff_nonspecial]
    by_cases h : 0 ≤ a - b
    · right
      rw [τ.s_dual]
      exact hMN.2 <| by
        rw [← abs_of_nonneg h]
        exact (le_abs_self N).trans <| (le_max_right _ _).trans hab
    · left
      push Not at h
      exact hMN.1 <| by
        have hMabs : |M| ≤ |a - b| := (le_max_left _ _).trans hab
        have hM : -|M| ≤ M := by
          have := le_abs_self (-M)
          rw [abs_neg] at this
          omega
        rw [abs_of_neg h] at hMabs
        omega

/-- The first auxiliary unboundedness set used for bounded-difference criteria. -/
def M : Set ℤ :=
  {m | ∃ a b : ℤ, τ.s a b > 0 ∧ m ≤ τ⁻¹.s b a}

/-- The second auxiliary unboundedness set used for bounded-difference criteria. -/
def M' : Set ℤ :=
  {m | ∃ n : ℤ, m ≤ n - τ n - τ.χ}

/-- The third auxiliary unboundedness set used for bounded-difference criteria. -/
def M'' : Set ℤ :=
  {m | ∃ a b : ℤ, τ.s a b > 0 ∧ m ≤ b - a - τ.χ + 1}


private lemma M'_sub_M : τ.M' ⊆ τ.M := by
  rintro m ⟨n, hn⟩
  use τ n + 1, n
  have : τ.s (τ n + 1) n = τ.s (τ n) n + 1 := by
    apply (τ.a_step_one_iff (τ n) n).2
    rw [τ.inv_mul_cancel_eval]
  rw [this]
  have hpos : τ.s (τ n) n ≥ 0 := τ.s_nonneg (τ n) n
  constructor
  · omega
  · rw [τ.s'_eq]
    omega

private lemma M''_sub_M' : τ.M'' ⊆ τ.M' := by
  rintro m ⟨a, b, hpos, mle⟩
  rw [τ.s_eq_se_card, gt_iff_lt] at hpos
  rw [Nat.cast_pos, Finset.card_pos] at hpos
  rcases hpos with ⟨n, hn⟩
  rw [τ.mem_se] at hn
  use n
  omega

private lemma M_sub_M'' : τ.M ⊆ τ.M'' := by
  rintro m ⟨a, b, hpos, mle⟩
  rw [τ.s_eq_se_card, gt_iff_lt] at hpos
  rw [Nat.cast_pos, Finset.card_pos] at hpos
  let n := Finset.max' _ hpos
  have hn : n ∈ τ.seFinset a b := Finset.max'_mem _ hpos
  obtain ⟨nge, τnlt⟩ := (τ.mem_se a b n).mp hn
  have s_zero : τ.s (τ n + 1) n = 1 := by
    calc
      τ.s (τ n + 1) n = τ.s (τ n) n + 1 := by
        apply (τ.a_step_one_iff (τ n) n).2
        simp only [τ.inv_mul_cancel_eval, le_refl]
      _ = 1 := by
        rw [τ.s_eq_se_card]
        have : τ.seFinset (τ n) n = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro m hm
          rw [τ.mem_se] at hm
          have b_le_m : b ≤ m := le_trans nge hm.1
          have τm_lt_a : τ m < a:= lt_trans hm.2 τnlt
          have m_se : m ∈ τ.seFinset a b := by
            simp_all
          have : m ≤ n := Finset.le_max' _ m m_se
          have m_eq_n : m = n := le_antisymm this hm.1
          simp_all
        rw [this, Finset.card_empty, Nat.cast_zero, zero_add]
  rw [τ.mem_se] at hn
  use τ n + 1, n
  constructor
  · simp_all
  · have mle' : m ≤ τ⁻¹.s n (τ n + 1) := by
      apply le_trans mle
      apply τ⁻¹.s.nondec (a := b) (b := a) (a' := n) (b' := τ n + 1) nge (by omega)
    rw [τ.s'_eq] at mle'
    obtain ⟨h1, h2⟩ := hn
    omega

/-- A set-theoretic reformulation of *Lemma 7.8* (`lem:malpha`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
lemma M'_eq_M : τ.M' = τ.M :=
  Set.Subset.antisymm τ.M'_sub_M <| Set.Subset.trans τ.M_sub_M'' τ.M''_sub_M'

/-- A set-theoretic reformulation of *Lemma 7.8* (`lem:malpha`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
lemma M''_eq_M : τ.M'' = τ.M :=
  Set.Subset.antisymm (Set.Subset.trans τ.M''_sub_M' τ.M'_sub_M) τ.M_sub_M''

private lemma bdiff_width_helper (M : ℤ) :
  (∀ n : ℤ, n - τ n ≤ M) ↔
   (∀ (a b : ℤ), M ≤ b - a → τ.s a b = 0) := by
  constructor
  · intro h a b hab
    by_contra hzero
    have hpos : τ.s a b > 0 :=
      lt_of_le_of_ne (τ.s_nonneg a b) (fun h => hzero h.symm)
    have : M - τ.χ + 1 ∈ τ.M' := by
      rw [τ.M'_eq_M, ← τ.M''_eq_M]
      use a, b
      exact ⟨hpos, by omega⟩
    rcases this with ⟨n, hn⟩
    have := h n
    omega
  · intro h n
    by_contra hn
    have : M - τ.χ + 1 ∈ τ.M'' := by
      rw [τ.M''_eq_M, ← τ.M'_eq_M]
      use n
      omega
    rcases this with ⟨a, b, hpos, hm⟩
    simp_all

/-- A permutation $\tau$ has bounded difference if and only if $s_\tau(a,b)$ agrees with
$\max\{0, a-b+\chi(\tau)\}$ for all $|a-b| \gg 0$. *Proposition 7.7*
(`prop:cliffordPerms`) of [An extended Demazure product](https://arxiv.org/abs/2206.14227),
part 1/2.* -/
theorem bdiff_iff_width : τ.isBdiff ↔ ∃ N, τ.width_bound N := by
  constructor
  · intro bdiff
    rcases bdiff with ⟨M, hM⟩
    rw [width_sides]
    use -M, M
    intro a b
    constructor <;> intro hab
    · have : ∀ (n : ℤ), n - τ n ≤ M := by
        intro n
        specialize hM n
        exact le_trans (le_abs_self (n - τ n)) hM
      rw [τ.bdiff_width_helper] at this
      apply this a b (by omega)
    · have : ∀ (n : ℤ), n - τ⁻¹ n ≤ M := by
        intro n
        specialize hM (τ⁻¹ n)
        rw [τ.mul_inv_cancel_eval] at hM
        have := le_trans (neg_le_abs (τ⁻¹ n - n)) hM
        omega
      rw [τ⁻¹.bdiff_width_helper] at this
      apply this b a hab
  · intro wb
    rw [width_sides] at wb
    rcases wb with ⟨M, N, hMN⟩
    have h_left_zero : ∀ (a b : ℤ), -M ≤ b - a → τ.s a b = 0 := by
      intro a b hab
      exact (hMN a b).1 (by omega)
    have h_left : ∀ n : ℤ, n - τ n ≤ -M := by
      rw [τ.bdiff_width_helper]
      exact h_left_zero
    have h_right_zero : ∀ (a b : ℤ), N ≤ b - a → τ⁻¹.s a b = 0 := by
      simp_all
    have h_right : ∀ n : ℤ, n - τ⁻¹ n ≤ N := by
      rw [τ⁻¹.bdiff_width_helper]
      exact h_right_zero
    use max (-M) N
    intro n
    have hle := h_left n
    have hge := h_right (τ n)
    rw [τ.inv_mul_cancel_eval] at hge
    rw [abs_le]
    constructor
    · omega
    · omega

/-- A permutation $\tau$ has bounded difference if and only if $s_\tau$ is a Clifford slipface.
*Proposition 7.7* (`prop:cliffordPerms`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
theorem bdiff_iff_clifford : τ.isBdiff ↔ τ.s.isClifford := by
  constructor
  · rintro ⟨M, hM⟩
    have M_nonneg : 0 ≤ M := (abs_nonneg (0 - τ 0)).trans (hM 0)
    use (2*M+1).toNat
    intro a b hsum
    rw [show (↑(2*M+1).toNat : ℤ) = 2*M+1 by omega] at hsum
    by_contra! hspecial
    have spos : τ.s a b > 0 := by
      apply lt_of_le_of_ne <| τ.s_nonneg a b
      intro h; exact hspecial.1 h.symm
    have s'pos : τ⁻¹.s b a > 0 := by
      rw [← τ.s_dual]
      apply lt_of_le_of_ne <| τ.s.dual.nonneg b a
      intro h; exact hspecial.2 h.symm
    have s'le : τ.s.dual b a ≤ M - τ.χ := by
      rw [τ.s_dual]
      have hmem : τ⁻¹.s b a ∈ τ.M := by exact ⟨a, b, spos, le_rfl⟩
      rw [← τ.M'_eq_M] at hmem
      rcases hmem with ⟨n, hn⟩
      have := le_trans (le_abs_self (n - τ n)) (hM n)
      omega
    have sle : τ.s a b ≤ M + τ.χ := by
      have hmem : τ.s a b ∈ τ⁻¹.M := by
        use b, a
        simp_all
      rw [← τ⁻¹.M'_eq_M] at hmem
      rcases hmem with ⟨n, hn⟩
      rw [τ.chi_dual] at hn
      have := hM (τ⁻¹ n); rw [τ.mul_inv_cancel_eval] at this
      have := le_trans (neg_le_abs (τ⁻¹ n - n)) this
      omega
    omega
  · rintro ⟨C, hC⟩; rw [τ.s_dual] at hC
    use C + 1 + |τ.χ|
    intro n
    by_contra! abs_gt
    by_cases h : n - τ n ≤ 0
    · rw [abs_of_nonpos h] at abs_gt
      have : (↑C) + (1 : ℤ) ∈ τ⁻¹.M' := by
        use τ n; rw [τ.inv_mul_cancel_eval, τ.chi_dual]
        have := neg_le_abs τ.χ
        omega
      rw [τ⁻¹.M'_eq_M] at this
      rcases this with ⟨b, a, hpos, hle⟩
      rw [inv_inv] at hle
      specialize hC a b (by omega)
      omega
    · rw [abs_of_pos (a := n - τ n) (by omega)] at abs_gt
      have : (↑C) + (1 : ℤ) ∈ τ.M' := by
        use n
        have := le_abs_self τ.χ
        omega
      rw [τ.M'_eq_M] at this
      rcases this with ⟨a, b, hpos, hle⟩
      specialize hC a b (by omega)
      omega

end AspPerm

end LeanPool.DemazureProduct
