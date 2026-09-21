/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Graph.Linear

/-!
# The triangle witness at q = Θ(1/t)

AUDIT-NOTES B2(ii) / Theorem `thm:trianglelinear`: with the corrected density of `Linear.lean` (`m = 3`, `c = 4`) the parity-perfect triangle target `Π(−q,−q,−q)` lies in the ancestral-independence feasible set of the triangle module at every order `t` for `q = 1/(16t)` (`triangle_linear_witness`). Everything here is proved.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## The triangle witness of Theorem `thm:trianglelinear`

The auxiliary development behind `triangle_linear_witness`: the copied observations
`A^{ij} = x_i z_j`, `B^{ik} = x_i y_k`, `C^{jk} = z_j y_k` as exclusive ors of the auxiliary
signs, the pushforward of `triDensity` along them, and the boundary computation of
Lemma `lem:boundary`. Every character prescribed by the diagonal law, by an injectable
marginal or by an ancestral-independence product has a boundary that is empty or meets two
sign families, so the correction of `triCoeff` never reaches it and `triW_moment` returns
the target value `(−q)^{|∂|/2}`. -/

namespace TriWitnessAux

open TriangleInflation

variable {t : ℕ}

/-! ### Signs and Walsh characters -/

/-- The sign of an exclusive or is the product of the signs. -/
theorem sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> norm_num [sgn]

/-! ### Pushforwards -/

theorem sum_mul_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) (f : β → ℝ) :
    ∑ b, f b * pushforward w F b = ∑ a, f (F a) * w a := by
  simp only [pushforward, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have : ∀ b : β, f b * (if F a = b then w a else 0) = if F a = b then f b * w a else 0 := by
    intro b; split <;> ring
  simp only [this]
  rw [Finset.sum_ite_eq (Finset.univ) (F a) (fun b => f b * w a)]
  simp

theorem pushforward_isLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {w : α → ℝ} (h : IsLaw w) (F : α → β) : IsLaw (pushforward w F) := by
  refine ⟨fun b => ?_, ?_⟩
  · exact Finset.sum_nonneg (fun a _ => by split; exacts [h.1 a, le_rfl])
  · have := sum_mul_pushforward w F (fun _ => (1 : ℝ))
    simpa [h.2] using this

/-- Fourier uniqueness transported along an identification of a finite type with a sign
cube. -/
theorem funext_of_walsh_moments_equiv {α : Type*} [Fintype α] [DecidableEq α]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : α ≃ (ι → Bool)) (P Q : α → ℝ)
    (h : ∀ S : Finset ι, ∑ a, walsh S (e a) * P a = ∑ a, walsh S (e a) * Q a) : P = Q := by
  have key : (fun w => P (e.symm w)) = (fun w => Q (e.symm w)) := by
    refine funext_of_walsh_moments _ _ (fun S => ?_)
    have hP : ∑ w : ι → Bool, walsh S w * P (e.symm w) = ∑ a, walsh S (e a) * P a :=
      (Equiv.sum_comp e (fun w => walsh S w * P (e.symm w))).symm.trans
        (Finset.sum_congr rfl (fun a _ => by rw [Equiv.symm_apply_apply]))
    have hQ : ∑ w : ι → Bool, walsh S w * Q (e.symm w) = ∑ a, walsh S (e a) * Q a :=
      (Equiv.sum_comp e (fun w => walsh S w * Q (e.symm w))).symm.trans
        (Finset.sum_congr rfl (fun a _ => by rw [Equiv.symm_apply_apply]))
    rw [hP, hQ]; exact h S
  funext a
  have := congrFun key (e a)
  simpa using this

/-! ### The copied observations of the triangle witness -/

/-- The auxiliary sign coordinate of a copied latent variable: `X_i ↦ (0,i)`, `Z_j ↦ (1,j)`,
`Y_k ↦ (2,k)`. -/
def latSign : Latent t → TriSign t
  | .X i => (0, i)
  | .Z j => (1, j)
  | .Y k => (2, k)

theorem latSign_injective : Function.Injective (latSign (t := t)) := by
  rintro (a | a | a) (b | b | b) h <;> simp [latSign, Prod.ext_iff] at h ⊢ <;> simp [h]

/-- The copied observations of the witness: `A^{ij} = x_i z_j`, `B^{ik} = x_i y_k`,
`C^{jk} = z_j y_k`, written as exclusive ors of the auxiliary signs. -/
def triObs (s : TriSign t → Bool) : Assign t
  | .A i j => xor (s (0, i)) (s (1, j))
  | .B i k => xor (s (0, i)) (s (2, k))
  | .C j k => xor (s (1, j)) (s (2, k))

/-! ### Moments of the density and of the target -/

theorem triDensity_moment (t : ℕ) (q : ℝ) (hq : 0 ≤ q) (S : Finset (TriSign t)) :
    ∑ s : TriSign t → Bool, walsh S s * triDensity t q s = triCoeff S * triMom q S.card := by
  have h2 : (2 : ℝ) ^ (3 * t) ≠ 0 := by positivity
  have hsum : ∑ s : TriSign t → Bool, walsh S s * triDensity t q s
      = (1 / 2 ^ (3 * t)) * ∑ s : TriSign t → Bool, walsh S s * triW t q s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by rw [triDensity]; ring)
  rw [hsum, triW_moment t q hq S]
  field_simp

/-! Moments of the parity-perfect target. -/

theorem triParity_mom0 (q : ℝ) : ∑ w : ThreeBit, triParity q w = 1 := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momA (q : ℝ) : ∑ w : ThreeBit, sgn w.1 * triParity q w = -q := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momB (q : ℝ) : ∑ w : ThreeBit, sgn w.2.1 * triParity q w = -q := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momC (q : ℝ) : ∑ w : ThreeBit, sgn w.2.2 * triParity q w = -q := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momAB (q : ℝ) :
    ∑ w : ThreeBit, sgn w.1 * sgn w.2.1 * triParity q w = -q := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momAC (q : ℝ) :
    ∑ w : ThreeBit, sgn w.1 * sgn w.2.2 * triParity q w = -q := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momBC (q : ℝ) :
    ∑ w : ThreeBit, sgn w.2.1 * sgn w.2.2 * triParity q w = -q := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

theorem triParity_momABC (q : ℝ) :
    ∑ w : ThreeBit, sgn w.1 * sgn w.2.1 * sgn w.2.2 * triParity q w = 1 := by
  simp [Fintype.sum_prod_type, triParity, sgn]
  ring

/-! ### The boundary of an injectable block -/

theorem walsh_pair {ι : Type*} [Fintype ι] [DecidableEq ι] {v w : ι} (h : v ≠ w)
    (s : ι → Bool) : walsh {v, w} s = sgn (s v) * sgn (s w) := by
  rw [walsh, Finset.prod_insert (by simpa using h), Finset.prod_singleton]

theorem pair_ne {v w : TriSign t} (h : v.1 ≠ w.1) : v ≠ w := fun hh => h (by rw [hh])

theorem pair_card {v w : TriSign t} (h : v.1 ≠ w.1) :
    ({v, w} : Finset (TriSign t)).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simpa using pair_ne h), Finset.card_singleton]

theorem pair_fam {v w : TriSign t} (h : v.1 ≠ w.1) :
    ∃ a ∈ ({v, w} : Finset (TriSign t)), ∃ b ∈ ({v, w} : Finset (TriSign t)), a.1 ≠ b.1 :=
  ⟨v, by simp, w, by simp, h⟩

theorem triMom_two (q : ℝ) : triMom q 2 = -q := by simp [triMom]

theorem triMom_zero (q : ℝ) : triMom q 0 = 1 := by simp [triMom]

/-- A subset of a three-element set is one of eight explicit sets. -/
theorem subset_triple {α : Type*} [DecidableEq α] {U : Finset α} {a b c : α}
    (h : U ⊆ {a, b, c}) :
    U = ∅ ∨ U = {a} ∨ U = {b} ∨ U = {c} ∨ U = {a, b} ∨ U = {a, c} ∨ U = {b, c} ∨
      U = {a, b, c} := by
  classical
  have hU : U = ({a, b, c} : Finset α).filter (fun x => x ∈ U) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨h hx, hx⟩, fun hx => hx.2⟩
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> by_cases hc : c ∈ U <;>
    rw [hU] <;>
      simp [Finset.filter_insert, Finset.filter_singleton, ha, hb, hc]

/-- The moment that the parity-perfect target prescribes for a set of copied
observations. -/
noncomputable def tgt (q : ℝ) (U : Finset (Obs t)) : ℝ :=
  ∑ w : ThreeBit, (∏ u ∈ U, sgn (partyBit u.party w)) * triParity q w

/-- The boundary of a subset of a copied triangle: an explicit set of auxiliary signs that
carries the character of the subset, lies inside the image of its copied ancestry, has even
cardinality, is empty or meets two families, and whose moment is the prescribed one. -/
theorem block_boundary (q : ℝ) (i j k : Fin t) (U : Finset (Obs t))
    (hU : U ⊆ copiedTriangle i j k) :
    ∃ B : Finset (TriSign t),
      (∀ s : TriSign t → Bool, ∏ u ∈ U, sgn (triObs s u) = walsh B s) ∧
      B ⊆ (ancestorsOf U).image latSign ∧
      B.card % 2 = 0 ∧
      (B = ∅ ∨ ∃ a ∈ B, ∃ b ∈ B, a.1 ≠ b.1) ∧
      triMom q B.card = tgt q U := by
  classical
  have hxz : ((0 : Fin 3), i).1 ≠ ((1 : Fin 3), j).1 := by
    show (0 : Fin 3) ≠ 1
    decide
  have hxy : ((0 : Fin 3), i).1 ≠ ((2 : Fin 3), k).1 := by
    show (0 : Fin 3) ≠ 2
    decide
  have hzy : ((1 : Fin 3), j).1 ≠ ((2 : Fin 3), k).1 := by
    show (1 : Fin 3) ≠ 2
    decide
  rcases subset_triple (a := Obs.A i j) (b := Obs.B i k) (c := Obs.C j k) hU with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨∅, fun s => by simp [walsh], by simp, by simp, Or.inl rfl,
      by simp [triMom_zero, tgt, triParity_mom0]⟩
  · refine ⟨{(0, i), (1, j)}, fun s => ?_, ?_, ?_, Or.inr (pair_fam hxz), ?_⟩
    · rw [Finset.prod_singleton, walsh_pair (pair_ne hxz)]
      simp [triObs, sgn_xor]
    · simp [ancestorsOf, Obs.ancestors, latSign]
    · rw [pair_card hxz]
    · rw [pair_card hxz, triMom_two, tgt]
      simp only [Finset.prod_singleton]
      exact (triParity_momA q).symm
  · refine ⟨{(0, i), (2, k)}, fun s => ?_, ?_, ?_, Or.inr (pair_fam hxy), ?_⟩
    · rw [Finset.prod_singleton, walsh_pair (pair_ne hxy)]
      simp [triObs, sgn_xor]
    · simp [ancestorsOf, Obs.ancestors, latSign]
    · rw [pair_card hxy]
    · rw [pair_card hxy, triMom_two, tgt]
      simp only [Finset.prod_singleton]
      exact (triParity_momB q).symm
  · refine ⟨{(1, j), (2, k)}, fun s => ?_, ?_, ?_, Or.inr (pair_fam hzy), ?_⟩
    · rw [Finset.prod_singleton, walsh_pair (pair_ne hzy)]
      simp [triObs, sgn_xor]
    · simp [ancestorsOf, Obs.ancestors, latSign]
    · rw [pair_card hzy]
    · rw [pair_card hzy, triMom_two, tgt]
      simp only [Finset.prod_singleton]
      exact (triParity_momC q).symm
  · refine ⟨{(1, j), (2, k)}, fun s => ?_, ?_, ?_, Or.inr (pair_fam hzy), ?_⟩
    · rw [Finset.prod_insert (by simp), Finset.prod_singleton, walsh_pair (pair_ne hzy)]
      simp only [triObs, sgn_xor]
      have h0 := sgn_mul_self (s (0, i))
      linear_combination (sgn (s (1, j)) * sgn (s (2, k))) * h0
    · simp [ancestorsOf, Obs.ancestors, latSign, Finset.image_insert]
    · rw [pair_card hzy]
    · rw [pair_card hzy, triMom_two, tgt]
      simp only [Finset.prod_insert (by simp : Obs.A i j ∉ ({Obs.B i k} : Finset (Obs t))),
        Finset.prod_singleton]
      rw [← triParity_momAB q]
      exact Finset.sum_congr rfl (fun w _ => by simp only [Obs.party, partyBit]; try ring)
  · refine ⟨{(0, i), (2, k)}, fun s => ?_, ?_, ?_, Or.inr (pair_fam hxy), ?_⟩
    · rw [Finset.prod_insert (by simp), Finset.prod_singleton, walsh_pair (pair_ne hxy)]
      simp only [triObs, sgn_xor]
      have h0 := sgn_mul_self (s (1, j))
      linear_combination (sgn (s (0, i)) * sgn (s (2, k))) * h0
    · simp [ancestorsOf, Obs.ancestors, latSign, Finset.image_insert]
    · rw [pair_card hxy]
    · rw [pair_card hxy, triMom_two, tgt]
      simp only [Finset.prod_insert (by simp : Obs.A i j ∉ ({Obs.C j k} : Finset (Obs t))),
        Finset.prod_singleton]
      rw [← triParity_momAC q]
      exact Finset.sum_congr rfl (fun w _ => by simp only [Obs.party, partyBit]; try ring)
  · refine ⟨{(0, i), (1, j)}, fun s => ?_, ?_, ?_, Or.inr (pair_fam hxz), ?_⟩
    · rw [Finset.prod_insert (by simp), Finset.prod_singleton, walsh_pair (pair_ne hxz)]
      simp only [triObs, sgn_xor]
      have h0 := sgn_mul_self (s (2, k))
      linear_combination (sgn (s (0, i)) * sgn (s (1, j))) * h0
    · simp [ancestorsOf, Obs.ancestors, latSign, Finset.image_insert,
        Finset.insert_subset_iff]
    · rw [pair_card hxz]
    · rw [pair_card hxz, triMom_two, tgt]
      simp only [Finset.prod_insert (by simp : Obs.B i k ∉ ({Obs.C j k} : Finset (Obs t))),
        Finset.prod_singleton]
      rw [← triParity_momBC q]
      exact Finset.sum_congr rfl (fun w _ => by simp only [Obs.party, partyBit]; try ring)
  · refine ⟨∅, fun s => ?_, by simp, by simp, Or.inl rfl, ?_⟩
    · rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      simp only [triObs, sgn_xor, walsh, Finset.prod_empty]
      have h0 := sgn_mul_self (s (0, i))
      have h1 := sgn_mul_self (s (1, j))
      have h2 := sgn_mul_self (s (2, k))
      linear_combination (sgn (s (1, j)) * sgn (s (1, j)) * sgn (s (2, k)) * sgn (s (2, k))) * h0
        + (sgn (s (2, k)) * sgn (s (2, k))) * h1 + h2
    · rw [Finset.card_empty, triMom_zero, tgt]
      simp only [Finset.prod_insert (by simp : Obs.A i j ∉ ({Obs.B i k, Obs.C j k} : Finset (Obs t))),
        Finset.prod_insert (by simp : Obs.B i k ∉ ({Obs.C j k} : Finset (Obs t))),
        Finset.prod_singleton]
      rw [← triParity_momABC q]
      exact Finset.sum_congr rfl (fun w _ => by simp only [Obs.party, partyBit]; try ring)

/-! ### The master character computation -/

theorem triMom_add (q : ℝ) {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    triMom q (a + b) = triMom q a * triMom q b := by
  have hab : (a + b) % 2 = 0 := by omega
  have hd : (a + b) / 2 = a / 2 + b / 2 := by omega
  simp [triMom, ha, hb, hab, hd, pow_add]

theorem triMom_sum {ι : Type*} [DecidableEq ι] (q : ℝ) (s : Finset ι) (c : ι → ℕ)
    (h : ∀ m ∈ s, c m % 2 = 0) :
    triMom q (∑ m ∈ s, c m) = ∏ m ∈ s, triMom q (c m) := by
  classical
  induction s using Finset.induction with
  | empty => simp [triMom]
  | insert a s ha ih =>
      have hrest : (∑ m ∈ s, c m) % 2 = 0 := by
        have : (2 : ℕ) ∣ ∑ m ∈ s, c m :=
          Finset.dvd_sum (fun i hi => by have := h i (Finset.mem_insert_of_mem hi); omega)
        omega
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        triMom_add q (h a (Finset.mem_insert_self a s)) hrest,
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

theorem triCoeff_eq_one (B : Finset (TriSign t))
    (h : B = ∅ ∨ ∃ a ∈ B, ∃ b ∈ B, a.1 ≠ b.1) : triCoeff B = 1 := by
  rcases h with rfl | ⟨a, ha, b, hb, hne⟩
  · simp [triCoeff]
  · have hB : B ≠ ∅ := fun hh => by simp [hh] at ha
    have hno : ¬ ∃ g : Fin 3, ∀ v ∈ B, v.1 = g := by
      rintro ⟨g, hg⟩
      exact hne ((hg a ha).trans (hg b hb).symm)
    rw [triCoeff, if_neg hB, if_neg hno]

/-- The witness law on the copied observations: the pushforward of the corrected density
along `A^{ij} = x_i z_j`, `B^{ik} = x_i y_k`, `C^{jk} = z_j y_k`. -/
noncomputable def triGamma (t : ℕ) (q : ℝ) : Assign t → ℝ :=
  pushforward (triDensity t q) triObs

/-- One injectable block: the character of any subset of a copied triangle has the moment
that the parity-perfect target prescribes. -/
theorem master1 (q : ℝ) (hq : 0 ≤ q) (i j k : Fin t) (U : Finset (Obs t))
    (hU : U ⊆ copiedTriangle i j k) :
    ∑ s : TriSign t → Bool, (∏ u ∈ U, sgn (triObs s u)) * triDensity t q s = tgt q U := by
  obtain ⟨B, hchar, _, _, hfam, hmom⟩ := block_boundary q i j k U hU
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [hchar s]),
    triDensity_moment t q hq B, triCoeff_eq_one B hfam, one_mul, hmom]

/-- Pairwise ancestrally independent injectable blocks: the joint character factorizes into
the prescribed moments. -/
theorem master (q : ℝ) (hq : 0 ≤ q) {n : ℕ} (S : Fin n → Finset (Obs t))
    (hinj : ∀ m, Injectable (S m))
    (hindep : ∀ m m', m ≠ m' → AncestrallyIndependent (S m) (S m'))
    (U : Fin n → Finset (Obs t)) (hUS : ∀ m, U m ⊆ S m) :
    ∑ s : TriSign t → Bool, (∏ m, ∏ u ∈ U m, sgn (triObs s u)) * triDensity t q s
      = ∏ m, tgt q (U m) := by
  classical
  have hblock : ∀ m : Fin n, ∃ B : Finset (TriSign t),
      (∀ s : TriSign t → Bool, ∏ u ∈ U m, sgn (triObs s u) = walsh B s) ∧
      B ⊆ (ancestorsOf (U m)).image latSign ∧
      B.card % 2 = 0 ∧
      (B = ∅ ∨ ∃ a ∈ B, ∃ b ∈ B, a.1 ≠ b.1) ∧
      triMom q B.card = tgt q (U m) := by
    intro m
    obtain ⟨i, j, k, hsub⟩ := hinj m
    exact block_boundary q i j k (U m) ((hUS m).trans hsub)
  choose B hchar hsub hcard hfam hmom using hblock
  have hanc : ∀ m, B m ⊆ (ancestorsOf (S m)).image latSign := by
    intro m
    refine (hsub m).trans (Finset.image_subset_image ?_)
    exact Finset.biUnion_subset_biUnion_of_subset_left _ (hUS m)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) B := by
    intro m _ m' _ hne
    have h0 : Disjoint (ancestorsOf (S m)) (ancestorsOf (S m')) := hindep m m' hne
    have h1 : Disjoint ((ancestorsOf (S m)).image latSign)
        ((ancestorsOf (S m')).image latSign) :=
      (Finset.disjoint_image latSign_injective).2 h0
    exact Finset.disjoint_of_subset_left (hanc m)
      (Finset.disjoint_of_subset_right (hanc m') h1)
  set BB : Finset (TriSign t) := Finset.univ.disjiUnion B hdisj with hBB
  have hwalsh : ∀ s : TriSign t → Bool, (∏ m, ∏ u ∈ U m, sgn (triObs s u)) = walsh BB s := by
    intro s
    rw [walsh, hBB, Finset.prod_disjiUnion]
    exact Finset.prod_congr rfl (fun m _ => (hchar m s).trans rfl)
  have hcoeff : triCoeff BB = 1 := by
    refine triCoeff_eq_one BB ?_
    by_cases hemp : BB = ∅
    · exact Or.inl hemp
    · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hemp
      rw [hBB, Finset.mem_disjiUnion] at hv
      obtain ⟨m, -, hvm⟩ := hv
      rcases hfam m with hme | ⟨a, ha, b, hb, hne⟩
      · exact absurd hvm (by simp [hme])
      · refine Or.inr ⟨a, ?_, b, ?_, hne⟩ <;>
          rw [hBB, Finset.mem_disjiUnion] <;>
          exact ⟨m, Finset.mem_univ m, by assumption⟩
  have hcards : BB.card = ∑ m : Fin n, (B m).card := by
    rw [hBB, Finset.card_disjiUnion]
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [hwalsh s]),
    triDensity_moment t q hq BB, hcoeff, one_mul, hcards,
    triMom_sum q Finset.univ (fun m => (B m).card) (fun m _ => hcard m)]
  exact Finset.prod_congr rfl (fun m _ => hmom m)

/-! ### Symmetry of the witness -/

/-- The permutation of copy indices attached to a sign family. -/
def famPerm (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    Fin 3 → Equiv.Perm (Fin t) :=
  fun g => if g = 0 then π.1 else if g = 1 then π.2.1 else π.2.2

/-- The induced permutation of the auxiliary signs. -/
def signPerm (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    Equiv.Perm (TriSign t) where
  toFun v := (v.1, famPerm π v.1 v.2)
  invFun v := (v.1, (famPerm π v.1).symm v.2)
  left_inv := by rintro ⟨g, i⟩; simp
  right_inv := by rintro ⟨g, i⟩; simp

/-- Relabelling the auxiliary signs, as a permutation of sign assignments. -/
def signPermFun (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    (TriSign t → Bool) ≃ (TriSign t → Bool) where
  toFun s := fun v => s (signPerm π v)
  invFun s := fun v => s ((signPerm π).symm v)
  left_inv := by intro s; funext v; simp
  right_inv := by intro s; funext v; simp

/-- The relabelling of copied observations, as a permutation. -/
def obsPerm (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    Equiv.Perm (Obs t) where
  toFun := Obs.perm π
  invFun := Obs.perm (π.1.symm, π.2.1.symm, π.2.2.symm)
  left_inv := by rintro (⟨i, j⟩ | ⟨i, k⟩ | ⟨j, k⟩) <;> simp [Obs.perm]
  right_inv := by rintro (⟨i, j⟩ | ⟨i, k⟩ | ⟨j, k⟩) <;> simp [Obs.perm]

theorem relabel_injective (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    Function.Injective (relabel (t := t) π) := by
  intro a b h
  funext u
  have h2 : a (Obs.perm π ((obsPerm π).symm u)) = b (Obs.perm π ((obsPerm π).symm u)) :=
    congrFun h ((obsPerm π).symm u)
  have h3 : Obs.perm π ((obsPerm π).symm u) = u := (obsPerm π).apply_symm_apply u
  rwa [h3] at h2

theorem triFactor_perm (t : ℕ) (q : ℝ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (s : TriSign t → Bool) (g : Fin 3) :
    triFactor t q (fun v => s (signPerm π v)) g = triFactor t q s g :=
  Equiv.prod_comp (famPerm π g) (fun i => triAtom q (s (g, i)))

theorem triDensity_perm (t : ℕ) (q : ℝ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (s : TriSign t → Bool) :
    triDensity t q (fun v => s (signPerm π v)) = triDensity t q s := by
  simp only [triDensity, triW, triFactor_perm]

theorem triObs_perm (t : ℕ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (s : TriSign t → Bool) :
    triObs (fun v => s (signPerm π v)) = relabel π (triObs s) := by
  funext u
  cases u <;> simp [triObs, relabel, Obs.perm, signPerm, famPerm]

theorem triGamma_isLaw (t : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16) :
    IsLaw (triGamma t q) :=
  pushforward_isLaw (triDensity_isLaw t q hq0 hq) triObs

theorem triGamma_symmetric (t : ℕ) (q : ℝ) : SymmetricLaw t (triGamma t q) := by
  intro π ω
  show ∑ s : TriSign t → Bool, (if triObs s = relabel π ω then triDensity t q s else 0)
      = ∑ s : TriSign t → Bool, (if triObs s = ω then triDensity t q s else 0)
  rw [← Equiv.sum_comp (signPermFun π)
    (fun s => if triObs s = relabel π ω then triDensity t q s else 0)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  show (if triObs (fun v => s (signPerm π v)) = relabel π ω then
      triDensity t q (fun v => s (signPerm π v)) else 0)
    = if triObs s = ω then triDensity t q s else 0
  rw [triObs_perm, triDensity_perm]
  by_cases h : triObs s = ω
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (relabel_injective π hh))]

/-! ### The injectable marginals -/

theorem triGamma_injectable (t : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    InjectableMarginals t (triGamma t q) (triParity q) := by
  classical
  rintro S ⟨i, j, k, hsub⟩
  refine funext_of_walsh_moments _ _ (fun U => ?_)
  have hinjv : ∀ x ∈ U, ∀ y ∈ U, (x : Obs t) = (y : Obs t) → x = y :=
    fun x _ y _ h => Subtype.ext h
  have hUS : U.image Subtype.val ⊆ copiedTriangle i j k := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨v, -, rfl⟩ := hu
    exact hsub v.2
  have himg : ∀ ω : Assign t,
      walsh U (restrictAssign S ω) = ∏ u ∈ U.image Subtype.val, sgn (ω u) := by
    intro ω
    rw [Finset.prod_image hinjv]
    rfl
  have hpr : ∀ w : ThreeBit,
      walsh U (partyRead S w) = ∏ u ∈ U.image Subtype.val, sgn (partyBit u.party w) := by
    intro w
    rw [Finset.prod_image hinjv]
    rfl
  have hL : ∑ s : TriSign t → Bool,
      walsh U (restrictAssign S (triObs s)) * triDensity t q s
      = tgt q (U.image Subtype.val) := by
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [himg (triObs s)])]
    exact master1 q hq i j k _ hUS
  have hR : ∑ w : ThreeBit, walsh U (partyRead S w) * triParity q w
      = tgt q (U.image Subtype.val) :=
    Finset.sum_congr rfl (fun w _ => by rw [hpr w])
  rw [sum_mul_pushforward (triGamma t q) (restrictAssign S) (walsh U),
    sum_mul_pushforward (triParity q) (partyRead S) (walsh U), triGamma,
    sum_mul_pushforward (triDensity t q) triObs
      (fun ω => walsh U (restrictAssign S ω)), hL, hR]

/-! ### The ancestral-independence products -/

/-- Uncurrying a family of sign assignments. -/
def sigmaFun {n : ℕ} (β : Fin n → Type) [∀ m, Fintype (β m)] :
    (∀ m, β m → Bool) ≃ ((Σ m, β m) → Bool) where
  toFun φ := fun x => φ x.1 x.2
  invFun u := fun m v => u ⟨m, v⟩
  left_inv _ := rfl
  right_inv u := funext (fun x => by cases x; rfl)

theorem triGamma_ancestral (t : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    AncestralProducts t (triGamma t q) (triParity q) := by
  classical
  intro n S hInj hIndep
  refine funext_of_walsh_moments_equiv (sigmaFun (fun m => (↥(S m) : Type))) _ _ (fun U => ?_)
  set V : ∀ m : Fin n, Finset ↥(S m) :=
    fun m => Finset.univ.filter (fun v => (⟨m, v⟩ : Σ m, ↥(S m)) ∈ U) with hV
  have hUV : U = Finset.univ.sigma V := by
    ext x
    obtain ⟨m, v⟩ := x
    simp [hV, Finset.mem_sigma]
  set W : Fin n → Finset (Obs t) := fun m => (V m).image Subtype.val with hW
  have hinjv : ∀ m : Fin n, ∀ x ∈ V m, ∀ y ∈ V m, (x : Obs t) = (y : Obs t) → x = y :=
    fun m x _ y _ h => Subtype.ext h
  have hWimg : ∀ (m : Fin n) (f : Obs t → ℝ), ∏ u ∈ W m, f u = ∏ v ∈ V m, f (v : Obs t) := by
    intro m f
    simp only [hW]
    exact Finset.prod_image (hinjv m)
  have hWS : ∀ m, W m ⊆ S m := by
    intro m u hu
    rw [hW, Finset.mem_image] at hu
    obtain ⟨v, -, rfl⟩ := hu
    exact v.2
  -- the character of `U` read on the copied observations
  have hchar : ∀ ω : Assign t,
      walsh U (sigmaFun (fun m => (↥(S m) : Type)) (fun m => restrictAssign (S m) ω))
        = ∏ m : Fin n, ∏ u ∈ W m, sgn (ω u) := by
    intro ω
    rw [walsh, hUV, Finset.prod_sigma]
    exact Finset.prod_congr rfl (fun m _ => (hWimg m (fun u => sgn (ω u))).symm)
  -- the character of `U` read on a family of sign assignments
  have hcharφ : ∀ φ : ∀ m : Fin n, ↥(S m) → Bool,
      walsh U (sigmaFun (fun m => (↥(S m) : Type)) φ)
        = ∏ m : Fin n, walsh (V m) (φ m) := by
    intro φ
    rw [walsh, hUV, Finset.prod_sigma]
    rfl
  -- the target side
  have htgt : ∀ m : Fin n,
      ∑ ψ : ↥(S m) → Bool, walsh (V m) ψ * pushforward (triParity q) (partyRead (S m)) ψ
        = tgt q (W m) := by
    intro m
    rw [sum_mul_pushforward (triParity q) (partyRead (S m)) (walsh (V m))]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [walsh, hWimg m (fun u => sgn (partyBit u.party w))]
    rfl
  have hR : ∑ φ : ∀ m : Fin n, ↥(S m) → Bool,
      walsh U (sigmaFun (fun m => (↥(S m) : Type)) φ)
        * ∏ m : Fin n, pushforward (triParity q) (partyRead (S m)) (φ m)
      = ∏ m : Fin n, tgt q (W m) := by
    rw [Finset.sum_congr rfl (fun φ (_ : φ ∈ Finset.univ) => by
      rw [hcharφ φ, ← Finset.prod_mul_distrib])]
    rw [← Fintype.prod_sum
      (fun (m : Fin n) (ψ : ↥(S m) → Bool) =>
        walsh (V m) ψ * pushforward (triParity q) (partyRead (S m)) ψ)]
    exact Finset.prod_congr rfl (fun m _ => htgt m)
  have hL : ∑ ω : Assign t,
      walsh U (sigmaFun (fun m => (↥(S m) : Type)) (fun m => restrictAssign (S m) ω))
        * triGamma t q ω
      = ∏ m : Fin n, tgt q (W m) := by
    rw [triGamma, sum_mul_pushforward (triDensity t q) triObs
      (fun ω => walsh U (sigmaFun (fun m => (↥(S m) : Type))
        (fun m => restrictAssign (S m) ω)))]
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [hchar (triObs s)])]
    exact master q hq S hInj hIndep W hWS
  rw [sum_mul_pushforward (triGamma t q) (fun ω m => restrictAssign (S m) ω)
    (fun φ => walsh U (sigmaFun (fun m => (↥(S m) : Type)) φ)), hL, hR]

/-! ### The diagonal law -/

/-- The bit that the `g`-th party reads off a three-bit outcome. -/
def bitOf : Fin 3 → ThreeBit → Bool :=
  fun g w => if g = 0 then w.1 else if g = 1 then w.2.1 else w.2.2

/-- The `g`-th copied observation of the diagonal triangle `Δ_{lll}`. -/
def obsDiag (l : Fin t) (g : Fin 3) : Obs t :=
  if g = 0 then Obs.A l l else if g = 1 then Obs.B l l else Obs.C l l

/-- The three diagonal outcomes, flattened into signs. -/
def flatD (t : ℕ) : (Fin t → ThreeBit) ≃ ((Σ _ : Fin t, Fin 3) → Bool) where
  toFun w := fun x => bitOf x.2 (w x.1)
  invFun u := fun l => (u ⟨l, 0⟩, u ⟨l, 1⟩, u ⟨l, 2⟩)
  left_inv w := by funext l; simp [bitOf]
  right_inv u := by
    funext x
    obtain ⟨l, g⟩ := x
    fin_cases g <;> rfl

theorem obsDiag_mem (l : Fin t) (g : Fin 3) : obsDiag l g ∈ copiedTriangle l l l := by
  fin_cases g <;> simp [obsDiag, copiedTriangle]

theorem obsDiag_injective (l : Fin t) : Function.Injective (obsDiag l) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [obsDiag]

theorem flatD_readDiagonal (ω : Assign t) (x : Σ _ : Fin t, Fin 3) :
    flatD t (readDiagonal ω) x = ω (obsDiag x.1 x.2) := by
  obtain ⟨l, g⟩ := x
  fin_cases g <;> rfl

theorem partyBit_obsDiag (l : Fin t) (g : Fin 3) (w : ThreeBit) :
    partyBit (obsDiag l g).party w = bitOf g w := by
  fin_cases g <;> rfl

theorem diagonalTriangle_indep {l l' : Fin t} (h : l ≠ l') :
    AncestrallyIndependent (diagonalTriangle l) (diagonalTriangle l') := by
  rw [AncestrallyIndependent, Finset.disjoint_left]
  intro a ha ha'
  simp only [ancestorsOf, diagonalTriangle, copiedTriangle, Obs.ancestors,
    Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at ha ha'
  obtain ⟨u, hu, hau⟩ := ha
  obtain ⟨u', hu', hau'⟩ := ha'
  rcases hu with rfl | rfl | rfl <;> rcases hu' with rfl | rfl | rfl <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hau hau' <;>
    rcases hau with rfl | rfl <;> rcases hau' with h1 | h1 <;> simp_all

theorem triGamma_diagonal (t : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    pushforward (triGamma t q) readDiagonal = tensorPow t (triParity q) := by
  classical
  refine funext_of_walsh_moments_equiv (flatD t) _ _ (fun U => ?_)
  set V : Fin t → Finset (Fin 3) :=
    fun l => Finset.univ.filter (fun g => (⟨l, g⟩ : Σ _ : Fin t, Fin 3) ∈ U) with hV
  have hUV : U = Finset.univ.sigma V := by
    ext x
    obtain ⟨l, g⟩ := x
    simp [hV, Finset.mem_sigma]
  set W : Fin t → Finset (Obs t) := fun l => (V l).image (obsDiag l) with hW
  have hWimg : ∀ (l : Fin t) (f : Obs t → ℝ),
      ∏ u ∈ W l, f u = ∏ g ∈ V l, f (obsDiag l g) := by
    intro l f
    simp only [hW]
    exact Finset.prod_image (fun a _ b _ h => obsDiag_injective l h)
  have hWS : ∀ l, W l ⊆ diagonalTriangle l := by
    intro l u hu
    rw [hW, Finset.mem_image] at hu
    obtain ⟨g, -, rfl⟩ := hu
    exact obsDiag_mem l g
  have hchar : ∀ ω : Assign t,
      walsh U (flatD t (readDiagonal ω)) = ∏ l : Fin t, ∏ u ∈ W l, sgn (ω u) := by
    intro ω
    rw [walsh, hUV, Finset.prod_sigma]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [hWimg l (fun u => sgn (ω u))]
    exact Finset.prod_congr rfl (fun g _ => by rw [flatD_readDiagonal])
  have hL : ∑ ω : Assign t, walsh U (flatD t (readDiagonal ω)) * triGamma t q ω
      = ∏ l : Fin t, tgt q (W l) := by
    rw [triGamma, sum_mul_pushforward (triDensity t q) triObs
      (fun ω => walsh U (flatD t (readDiagonal ω)))]
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => by rw [hchar (triObs s)])]
    exact master q hq (fun l => diagonalTriangle l) (fun l => ⟨l, l, l, subset_rfl⟩)
      (fun l l' h => diagonalTriangle_indep h) W hWS
  have hR : ∑ w : Fin t → ThreeBit, walsh U (flatD t w) * tensorPow t (triParity q) w
      = ∏ l : Fin t, tgt q (W l) := by
    have hstep : ∀ w : Fin t → ThreeBit,
        walsh U (flatD t w) * tensorPow t (triParity q) w
          = ∏ l : Fin t, ((∏ g ∈ V l, sgn (bitOf g (w l))) * triParity q (w l)) := by
      intro w
      rw [Finset.prod_mul_distrib, walsh, hUV, Finset.prod_sigma, tensorPow]
      rfl
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hstep w)]
    rw [← Fintype.prod_sum
      (fun (l : Fin t) (v : ThreeBit) => (∏ g ∈ V l, sgn (bitOf g v)) * triParity q v)]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [tgt]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [hWimg l (fun u => sgn (partyBit u.party v))]
    exact congrArg (· * triParity q v)
      (Finset.prod_congr rfl (fun g _ => by rw [partyBit_obsDiag]))
  rw [sum_mul_pushforward (triGamma t q) readDiagonal (fun w => walsh U (flatD t w)), hL, hR]

end TriWitnessAux

/-- AUDIT-NOTES B2(ii), stated in the triangle types of `TriangleInflation` so that it
can be proved against the existing definitions. With the `m = 3`, `c = 4` density (`W ≥ 3/5`
for `tq ≤ 1/16`) and `A^{ij} = x_i z_j`, `B^{ik} = x_i y_k`, `C^{jk} = z_j y_k`, the
parity-perfect target `Π(−q,−q,−q)` lies in `I^AI_t` for `q = 1/(16t)`.

AUDIT-NOTES records this as a new consequence, not claimed in the packet, which "MUST be
confirmed by the exact checker at `t = 1, 2, 3` (positivity of every atom of the witness,
symmetry, full diagonal law, all AI character equalities) before it enters the paper". -/
theorem triangle_linear_witness (t : ℕ) (ht : 1 ≤ t) (q : ℝ) (hq : q = 1 / (16 * (t : ℝ))) :
    TriangleInflation.AIFeasible t (triParity q) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqt : (t : ℝ) * q = 1 / 16 := by rw [hq]; field_simp
  exact ⟨TriWitnessAux.triGamma t q,
    TriWitnessAux.triGamma_isLaw t q hq0 (le_of_eq hqt),
    TriWitnessAux.triGamma_symmetric t q,
    TriWitnessAux.triGamma_diagonal t q hq0,
    TriWitnessAux.triGamma_injectable t q hq0,
    TriWitnessAux.triGamma_ancestral t q hq0⟩



end TriangleInflation.Graph
