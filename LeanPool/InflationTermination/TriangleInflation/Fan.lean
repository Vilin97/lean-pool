/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation.Main

/-!
# Finite-order fan inequalities

Statements for paper Section 5.4: Theorem 5.11 (`thm:fan`) with its pointwise certificate
(eq:fan-pointwise) and rejecting-order corollary (eq:fan-order), and Proposition 5.12
(`prop:Rp`). Proofs are deferred.
-/

@[expose] public section

namespace TriangleInflation

open Finset

/-- The indicator value of a Boolean, as a natural number. -/
def ind (b : Bool) : ℕ := if b then 1 else 0

/-! ### Arithmetic helpers for the pointwise certificate -/

private lemma ind_le_one (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]

private lemma three_mul_le_two_add_sq (S : ℕ) : 3 * S ≤ 2 + S * S := by
  rcases Nat.lt_or_ge S 3 with h | h
  · interval_cases S <;> norm_num
  · have h2 : 3 * S ≤ S * S := Nat.mul_le_mul h (le_refl S)
    omega

private lemma sum_offDiag_add_diag {t : ℕ} (f : Fin t → Fin t → ℕ) :
    (∑ k : Fin t, ∑ l : Fin t, if k = l then 0 else f k l) + ∑ k : Fin t, f k k
      = ∑ k : Fin t, ∑ l : Fin t, f k l := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (∑ l : Fin t, if k = l then f k l else 0) = f k k := by simp
  rw [← hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k = l <;> simp [hkl]

private lemma two_choose_two (t : ℕ) : 2 * t.choose 2 = t * (t - 1) := by
  induction t with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ n =>
      have hn : n + 1 - 1 = n := by omega
      rw [hn] at ih
      zify at ih ⊢
      linarith

/-- Paper equation (eq:fan-pointwise), multiplied by two to stay inside `ℕ`: for every
deterministic assignment of the fan `{A^{11}} ∪ {B^{1k}, C^{1k} : k ∈ [t]}`, with
`a = 𝟙[A^{11} = 0]`, `b k = 𝟙[B^{1k} = 0]`, `c k = 𝟙[C^{1k} = 0]`,
`∑_k a b_k c_k ≤ a + ½ ∑_{k ≠ l} b_k c_l`. -/
theorem fan_pointwise (t : ℕ) (a : Bool) (b c : Fin t → Bool) :
    2 * ∑ k : Fin t, ind a * ind (b k) * ind (c k)
      ≤ 2 * ind a + ∑ k : Fin t, ∑ l : Fin t, if k = l then 0 else ind (b k) * ind (c l) := by
  cases a with
  | false => simp [ind]
  | true =>
    have hone : ind true = 1 := rfl
    have hL : ∑ k : Fin t, ind true * ind (b k) * ind (c k)
        = ∑ k : Fin t, ind (b k) * ind (c k) :=
      Finset.sum_congr rfl fun k _ => by rw [hone, one_mul]
    rw [hL, hone]
    have hB : ∑ k : Fin t, ind (b k) * ind (c k) ≤ ∑ k : Fin t, ind (b k) :=
      Finset.sum_le_sum fun k _ => by
        calc ind (b k) * ind (c k) ≤ ind (b k) * 1 :=
              Nat.mul_le_mul (le_refl (ind (b k))) (ind_le_one (c k))
          _ = ind (b k) := mul_one _
    have hC : ∑ k : Fin t, ind (b k) * ind (c k) ≤ ∑ l : Fin t, ind (c l) :=
      Finset.sum_le_sum fun k _ => by
        calc ind (b k) * ind (c k) ≤ 1 * ind (c k) :=
              Nat.mul_le_mul (ind_le_one (b k)) (le_refl (ind (c k)))
          _ = ind (c k) := one_mul _
    have hsum := sum_offDiag_add_diag (fun k l => ind (b k) * ind (c l))
    have hmul : ∑ k : Fin t, ∑ l : Fin t, ind (b k) * ind (c l)
        = (∑ k : Fin t, ind (b k)) * (∑ l : Fin t, ind (c l)) :=
      (Finset.sum_mul_sum _ _ _ _).symm
    obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ,
        3 * (∑ k : Fin t, ind (b k) * ind (c k)) ≤ 2 + M ∧
          M ≤ (∑ k : Fin t, ∑ l : Fin t, if k = l then 0 else ind (b k) * ind (c l))
                + ∑ k : Fin t, ind (b k) * ind (c k) := by
      refine ⟨(∑ k : Fin t, ind (b k) * ind (c k)) * (∑ k : Fin t, ind (b k) * ind (c k)),
        three_mul_le_two_add_sq _, ?_⟩
      rw [hsum, hmul]
      exact Nat.mul_le_mul hB hC
    omega

noncomputable
section

/-! ### Real-valued indicators -/

/-- The indicator value of a Boolean, as a real number. -/
private def indR (b : Bool) : ℝ := if b then 1 else 0

private lemma indR_cast (b : Bool) : ((ind b : ℕ) : ℝ) = indR b := by
  cases b <;> simp [ind, indR]

private lemma indR_nonneg (b : Bool) : 0 ≤ indR b := by cases b <;> norm_num [indR]

private lemma indR_mul_self (b : Bool) : indR b * indR b = indR b := by
  cases b <;> norm_num [indR]

private lemma tri_sq (a b c : Bool) :
    (indR a * indR b * indR c) * (indR a * indR b * indR c) = indR a * indR b * indR c := by
  cases a <;> cases b <;> cases c <;> norm_num [indR]

private lemma tri_mul_root (a b c : Bool) :
    (indR a * indR b * indR c) * indR a = indR a * indR b * indR c := by
  cases a <;> cases b <;> cases c <;> norm_num [indR]

private lemma tri_mul_tri_le (a b c b' c' : Bool) :
    (indR a * indR b * indR c) * (indR a * indR b' * indR c') ≤ indR b * indR c' := by
  cases a <;> cases b <;> cases c <;> cases b' <;> cases c' <;> norm_num [indR]

/-- The real-valued form of the pointwise fan certificate. -/
private lemma fan_pointwise_real (t : ℕ) (a : Bool) (b c : Fin t → Bool) :
    2 * ∑ k : Fin t, indR a * indR (b k) * indR (c k)
      ≤ 2 * indR a + ∑ k : Fin t, ∑ l : Fin t, if k = l then 0 else indR (b k) * indR (c l) := by
  have h := fan_pointwise t a b c
  have h2 : ((2 * ∑ k : Fin t, ind a * ind (b k) * ind (c k) : ℕ) : ℝ)
      ≤ ((2 * ind a + ∑ k : Fin t, ∑ l : Fin t,
            if k = l then 0 else ind (b k) * ind (c l) : ℕ) : ℝ) := Nat.cast_le.mpr h
  push_cast [indR_cast] at h2
  exact h2

private lemma choose_two_real (t : ℕ) (ht : 1 ≤ t) :
    2 * (t.choose 2 : ℝ) = (t : ℝ) * (t : ℝ) - (t : ℝ) := by
  have h := two_choose_two t
  have h' : ((2 * t.choose 2 : ℕ) : ℝ) = ((t * (t - 1) : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ht] at h'
  push_cast at h'
  linarith

/-! ### Elementary expectation calculus -/

private lemma expect_sum {α ι : Type*} [Fintype α] [Fintype ι] (w : α → ℝ) (G : ι → α → ℝ) :
    ∑ a, w a * (∑ i, G i a) = ∑ i, ∑ a, w a * G i a := by
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

private lemma expect_sum2 {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ] (w : α → ℝ)
    (G : ι → κ → α → ℝ) :
    ∑ a, w a * (∑ i, ∑ j, G i j a) = ∑ i, ∑ j, ∑ a, w a * G i j a := by
  rw [expect_sum]
  exact Finset.sum_congr rfl fun i _ => expect_sum w (G i)

private lemma expect_smul {α : Type*} [Fintype α] (w : α → ℝ) (c : ℝ) (G : α → ℝ) :
    ∑ a, w a * (c * G a) = c * ∑ a, w a * G a := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

private lemma expect_add {α : Type*} [Fintype α] (w : α → ℝ) (G H : α → ℝ) :
    ∑ a, w a * (G a + H a) = (∑ a, w a * G a) + ∑ a, w a * H a := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

private lemma expect_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) (H : β → ℝ) :
    ∑ a, w a * H (F a) = ∑ b, pushforward w F b * H b := by
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp

/-- Cauchy–Schwarz for a nonnegative weight against an indicator-supported function. -/
private lemma cauchy_ind {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    (I U : α → ℝ) (hIU : ∀ x, U x * I x = U x) (hII : ∀ x, I x * I x = I x) :
    (∑ x, w x * U x) ^ 2 ≤ (∑ x, w x * I x) * (∑ x, w x * U x ^ 2) := by
  have key : ∀ y : ℝ,
      0 ≤ (∑ x, w x * I x) * (y * y) + (-2 * ∑ x, w x * U x) * y + (∑ x, w x * U x ^ 2) := by
    intro y
    have expand : ∑ x, w x * (U x - y * I x) ^ 2
        = (∑ x, w x * I x) * (y * y) + (-2 * ∑ x, w x * U x) * y + (∑ x, w x * U x ^ 2) := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have e : (U x - y * I x) ^ 2
          = U x ^ 2 - 2 * y * (U x * I x) + y ^ 2 * (I x * I x) := by ring
      rw [e, hIU x, hII x]; ring
    rw [← expand]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-! ### Transport along the symmetry group -/

private def relabelEquiv {t : ℕ}
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) : Assign t ≃ Assign t where
  toFun := relabel π
  invFun := relabel (π.1⁻¹, π.2.1⁻¹, π.2.2⁻¹)
  left_inv := by
    intro ω
    funext v
    cases v <;> simp [relabel, Obs.perm]
  right_inv := by
    intro ω
    funext v
    cases v <;> simp [relabel, Obs.perm]

private lemma symm_transport {t : ℕ} {Γ : Assign t → ℝ} (hs : SymmetricLaw t Γ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (G : Assign t → ℝ) :
    ∑ ω, Γ ω * G (relabel π ω) = ∑ ω, Γ ω * G ω := by
  have h := Equiv.sum_comp (relabelEquiv π) (fun ω => Γ ω * G ω)
  simp only [relabelEquiv, Equiv.coe_fn_mk, hs π] at h
  exact h

/-! ### Marginals of the tensor power -/

private lemma sum_prod_univ {ι κ : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ]
    (g : ι → κ → ℝ) : ∑ f : ι → κ, ∏ i, g i (f i) = ∏ i, ∑ j, g i j := by
  simpa using Finset.sum_prod_piFinset (Finset.univ : Finset κ) g

private lemma tensorPow_expect {t : ℕ} {P : ThreeBit → ℝ} (F : Fin t → ThreeBit → ℝ) :
    ∑ v : Fin t → ThreeBit, tensorPow t P v * ∏ l, F l (v l) = ∏ l, ∑ w, P w * F l w := by
  rw [← sum_prod_univ (fun l w => P w * F l w)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [tensorPow, Finset.prod_mul_distrib]

private lemma tensorPow_marg_one {t : ℕ} {P : ThreeBit → ℝ} (hP : IsLaw P) (i : Fin t)
    (g : ThreeBit → ℝ) :
    ∑ v : Fin t → ThreeBit, tensorPow t P v * g (v i) = ∑ w, P w * g w := by
  have key := tensorPow_expect (P := P) (fun l w => if l = i then g w else 1)
  have h1 : ∀ v : Fin t → ThreeBit, (∏ l, (if l = i then g (v l) else 1)) = g (v i) := by
    intro v; simp
  have h2 : ∀ l : Fin t, (∑ w, P w * (if l = i then g w else 1))
      = if l = i then (∑ w, P w * g w) else 1 := by
    intro l; by_cases hl : l = i <;> simp [hl, hP.2]
  simp only [h1, h2] at key
  rw [key]
  simp

private lemma tensorPow_marg_two {t : ℕ} {P : ThreeBit → ℝ} (hP : IsLaw P) {i j : Fin t}
    (hij : i ≠ j) (g h : ThreeBit → ℝ) :
    ∑ v : Fin t → ThreeBit, tensorPow t P v * (g (v i) * h (v j))
      = (∑ w, P w * g w) * (∑ w, P w * h w) := by
  have key := tensorPow_expect (P := P)
    (fun l w => (if l = i then g w else 1) * (if l = j then h w else 1))
  have h1 : ∀ v : Fin t → ThreeBit,
      (∏ l, ((if l = i then g (v l) else 1) * (if l = j then h (v l) else 1)))
        = g (v i) * h (v j) := by
    intro v; rw [Finset.prod_mul_distrib]; simp
  have h2 : ∀ l : Fin t,
      (∑ w, P w * ((if l = i then g w else 1) * (if l = j then h w else 1)))
        = if l = i then (∑ w, P w * g w) else if l = j then (∑ w, P w * h w) else 1 := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [hij]
    · by_cases hlj : l = j <;> simp [hli, hlj, hP.2, Ne.symm hij]
  simp only [h1, h2] at key
  rw [key,
    Finset.prod_eq_mul_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij
      (fun c _ hc => by simp [hc.1, hc.2])]
  simp [hij.symm]

/-! ### The fan expectations -/

/-- The indicator that the copied observation `v` reads `0`. -/
private def fanInd {t : ℕ} (v : Obs t) (ω : Assign t) : ℝ := indR (!(ω v))

private lemma fanInd_nonneg {t : ℕ} (v : Obs t) (ω : Assign t) : 0 ≤ fanInd v ω :=
  indR_nonneg _

private lemma fanInd_tri_sq {t : ℕ} (u v w : Obs t) (ω : Assign t) :
    (fanInd u ω * fanInd v ω * fanInd w ω) * (fanInd u ω * fanInd v ω * fanInd w ω)
      = fanInd u ω * fanInd v ω * fanInd w ω := tri_sq _ _ _

private lemma fanInd_tri_root {t : ℕ} (u v w : Obs t) (ω : Assign t) :
    (fanInd u ω * fanInd v ω * fanInd w ω) * fanInd u ω
      = fanInd u ω * fanInd v ω * fanInd w ω := tri_mul_root _ _ _

private lemma fanInd_tri_le {t : ℕ} (u v w v' w' : Obs t) (ω : Assign t) :
    (fanInd u ω * fanInd v ω * fanInd w ω) * (fanInd u ω * fanInd v' ω * fanInd w' ω)
      ≤ fanInd v ω * fanInd w' ω := tri_mul_tri_le _ _ _ _ _

private lemma fan_pointwise_fanInd {t : ℕ} (root : Obs t) (S T : Fin t → Obs t) (ω : Assign t) :
    2 * ∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
      ≤ 2 * fanInd root ω
          + ∑ k : Fin t, ∑ l : Fin t, if k = l then 0 else fanInd (S k) ω * fanInd (T l) ω :=
  fan_pointwise_real t (!(ω root)) (fun k => !(ω (S k))) (fun k => !(ω (T k)))

/-- The diagonal copy of a party at index `m`. -/
private def obsDiag {t : ℕ} : Party → Fin t → Obs t
  | .A, m => Obs.A m m
  | .B, m => Obs.B m m
  | .C, m => Obs.C m m

/-- The zero marginal of a party. -/
private def margP (p : Party) (P : ThreeBit → ℝ) : ℝ :=
  ∑ w : ThreeBit, P w * indR (!(partyBit p w))

private lemma margP_A (P : ThreeBit → ℝ) : margP Party.A P = margA P := by
  simp [margP, margA, partyBit, indR, Fintype.sum_prod_type]

private lemma margP_B (P : ThreeBit → ℝ) : margP Party.B P = margB P := by
  simp [margP, margB, partyBit, indR, Fintype.sum_prod_type]

private lemma margP_C (P : ThreeBit → ℝ) : margP Party.C P = margC P := by
  simp [margP, margC, partyBit, indR, Fintype.sum_prod_type]

private lemma partyBit_readDiagonal {t : ℕ} (p : Party) (m : Fin t) (ω : Assign t) :
    partyBit p (readDiagonal ω m) = ω (obsDiag p m) := by
  cases p <;> rfl

private lemma expect_single {t : ℕ} {Γ : Assign t → ℝ} {P : ThreeBit → ℝ} (hP : IsLaw P)
    (hd : pushforward Γ readDiagonal = tensorPow t P) (hs : SymmetricLaw t Γ)
    (p : Party) (m : Fin t)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (u : Obs t)
    (hu : Obs.perm π (obsDiag p m) = u) :
    ∑ ω, Γ ω * fanInd u ω = margP p P := by
  subst hu
  have h1 := symm_transport hs π (fun ω => fanInd (obsDiag p m) ω)
  simp only [relabel, fanInd] at h1
  rw [show (∑ ω, Γ ω * fanInd (Obs.perm π (obsDiag p m)) ω)
      = ∑ ω, Γ ω * indR (!(ω (Obs.perm π (obsDiag p m)))) from rfl, h1]
  have h2 := expect_pushforward Γ readDiagonal (fun v => indR (!(partyBit p (v m))))
  simp only [partyBit_readDiagonal] at h2
  rw [show (∑ ω, Γ ω * indR (!(ω (obsDiag p m))))
      = ∑ ω, Γ ω * indR (!(ω (obsDiag p m))) from rfl, h2, hd,
    tensorPow_marg_one hP m (fun w => indR (!(partyBit p w)))]
  rfl

private lemma expect_triple {t : ℕ} {Γ : Assign t → ℝ} {P : ThreeBit → ℝ} (hP : IsLaw P)
    (hd : pushforward Γ readDiagonal = tensorPow t P) (hs : SymmetricLaw t Γ) (m : Fin t)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (u v w : Obs t)
    (hu : Obs.perm π (Obs.A m m) = u) (hv : Obs.perm π (Obs.B m m) = v)
    (hw : Obs.perm π (Obs.C m m) = w) :
    ∑ ω, Γ ω * (fanInd u ω * fanInd v ω * fanInd w ω) = atom000 P := by
  subst hu; subst hv; subst hw
  have h1 := symm_transport hs π
    (fun ω => fanInd (Obs.A m m) ω * fanInd (Obs.B m m) ω * fanInd (Obs.C m m) ω)
  simp only [relabel, fanInd] at h1
  rw [show (∑ ω, Γ ω * (fanInd (Obs.perm π (Obs.A m m)) ω * fanInd (Obs.perm π (Obs.B m m)) ω
        * fanInd (Obs.perm π (Obs.C m m)) ω))
      = ∑ ω, Γ ω * (indR (!(ω (Obs.perm π (Obs.A m m)))) * indR (!(ω (Obs.perm π (Obs.B m m))))
        * indR (!(ω (Obs.perm π (Obs.C m m))))) from rfl, h1]
  have h2 := expect_pushforward Γ readDiagonal
    (fun v => indR (!(v m).1) * indR (!(v m).2.1) * indR (!(v m).2.2))
  simp only [readDiagonal, readTriangle] at h2
  rw [h2, hd, tensorPow_marg_one hP m
    (fun w => indR (!w.1) * indR (!w.2.1) * indR (!w.2.2))]
  simp [atom000, indR, Fintype.sum_prod_type]

private lemma expect_pair {t : ℕ} {Γ : Assign t → ℝ} {P : ThreeBit → ℝ} (hP : IsLaw P)
    (hd : pushforward Γ readDiagonal = tensorPow t P) (hs : SymmetricLaw t Γ)
    (p q : Party) {m m' : Fin t} (hmm : m ≠ m')
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (u v : Obs t)
    (hu : Obs.perm π (obsDiag p m) = u) (hv : Obs.perm π (obsDiag q m') = v) :
    ∑ ω, Γ ω * (fanInd u ω * fanInd v ω) = margP p P * margP q P := by
  subst hu; subst hv
  have h1 := symm_transport hs π
    (fun ω => fanInd (obsDiag p m) ω * fanInd (obsDiag q m') ω)
  simp only [relabel, fanInd] at h1
  rw [show (∑ ω, Γ ω * (fanInd (Obs.perm π (obsDiag p m)) ω * fanInd (Obs.perm π (obsDiag q m')) ω))
      = ∑ ω, Γ ω * (indR (!(ω (Obs.perm π (obsDiag p m))))
          * indR (!(ω (Obs.perm π (obsDiag q m'))))) from rfl, h1]
  have h2 := expect_pushforward Γ readDiagonal
    (fun v => indR (!(partyBit p (v m))) * indR (!(partyBit q (v m'))))
  simp only [partyBit_readDiagonal] at h2
  rw [h2, hd, tensorPow_marg_two hP hmm (fun w => indR (!(partyBit p w)))
    (fun w => indR (!(partyBit q w)))]
  rfl

/-! ### The abstract fan inequalities -/

private lemma fan_abstract {t : ℕ} (ht : 1 ≤ t) {Γ : Assign t → ℝ} (hΓ : IsLaw Γ)
    {z mR mS mT : ℝ} {root : Obs t} {S T : Fin t → Obs t}
    (h1 : ∑ ω, Γ ω * fanInd root ω = mR)
    (h2 : ∀ k, ∑ ω, Γ ω * (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω) = z)
    (h3 : ∀ k l, k ≠ l → ∑ ω, Γ ω * (fanInd (S k) ω * fanInd (T l) ω) = mS * mT) :
    (t : ℝ) * z ≤ mR + (t.choose 2 : ℝ) * (mS * mT) ∧
      (t : ℝ) * (z ^ 2 - mR * mS * mT) ≤ mR * z - mR * mS * mT := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hEU : (∑ ω, Γ ω * ∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω))
      = (t : ℝ) * z := by
    rw [expect_sum]
    simp [h2]
  have hmR : 0 ≤ mR := by
    rw [← h1]
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (hΓ.1 ω) (fanInd_nonneg _ _)
  -- the first inequality
  have hfan : (∑ ω, Γ ω * (2 * ∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)))
      ≤ ∑ ω, Γ ω * (2 * fanInd root ω
          + ∑ k : Fin t, ∑ l : Fin t, if k = l then 0 else fanInd (S k) ω * fanInd (T l) ω) :=
    Finset.sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (fan_pointwise_fanInd root S T ω) (hΓ.1 ω)
  have hoff : ∀ k l : Fin t,
      (∑ ω, Γ ω * (if k = l then 0 else fanInd (S k) ω * fanInd (T l) ω))
        = if k = l then 0 else mS * mT := by
    intro k l
    by_cases hkl : k = l
    · simp [hkl]
    · simp only [ite_eq_right hkl]; exact h3 k l hkl
  have hoffsum : (∑ k : Fin t, ∑ l : Fin t, if k = l then (0 : ℝ) else mS * mT)
      = ((t : ℝ) * t - t) * (mS * mT) := by
    have inner : ∀ k : Fin t, (∑ l : Fin t, if k = l then (0 : ℝ) else mS * mT)
        = (t : ℝ) * (mS * mT) - mS * mT := by
      intro k
      have e : ∀ l : Fin t, (if k = l then (0 : ℝ) else mS * mT)
          = mS * mT - (if k = l then mS * mT else 0) := by
        intro l; by_cases hkl : k = l <;> simp [hkl]
      simp only [e]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.sum_ite_eq]
      simp
    simp only [inner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [expect_smul, hEU, expect_add, expect_smul, h1, expect_sum2] at hfan
  simp only [hoff] at hfan
  rw [hoffsum] at hfan
  refine ⟨?_, ?_⟩
  · have hc := choose_two_real t ht
    rw [← hc] at hfan
    linarith
  · -- Cauchy–Schwarz
    have hIU : ∀ ω : Assign t,
        (∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)) * fanInd root ω
          = ∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω) := by
      intro ω
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => fanInd_tri_root _ _ _ _
    have hII : ∀ ω : Assign t, fanInd root ω * fanInd root ω = fanInd root ω :=
      fun ω => indR_mul_self _
    have hcs := cauchy_ind hΓ.1 (fanInd root)
      (fun ω => ∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)) hIU hII
    rw [hEU, h1] at hcs
    have hQ : (∑ ω, Γ ω * (∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)) ^ 2)
        ≤ (t : ℝ) * z + ((t : ℝ) * t - t) * (mS * mT) := by
      have expand : ∀ ω : Assign t,
          (∑ k : Fin t, (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)) ^ 2
            = ∑ k : Fin t, ∑ l : Fin t,
                (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
                  * (fanInd root ω * fanInd (S l) ω * fanInd (T l) ω) := by
        intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
      simp only [expand]
      rw [expect_sum2]
      have bound : ∀ k l : Fin t,
          (∑ ω, Γ ω * ((fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
              * (fanInd root ω * fanInd (S l) ω * fanInd (T l) ω)))
            ≤ if k = l then z else mS * mT := by
        intro k l
        by_cases hkl : k = l
        · subst hkl
          rw [ite_eq_left rfl]
          have e : ∀ ω : Assign t,
              (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
                  * (fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
                = fanInd root ω * fanInd (S k) ω * fanInd (T k) ω :=
            fun ω => fanInd_tri_sq _ _ _ _
          simp only [e]
          exact le_of_eq (h2 k)
        · rw [ite_eq_right hkl]
          calc (∑ ω, Γ ω * ((fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
                  * (fanInd root ω * fanInd (S l) ω * fanInd (T l) ω)))
              ≤ ∑ ω, Γ ω * (fanInd (S k) ω * fanInd (T l) ω) :=
                Finset.sum_le_sum fun ω _ =>
                  mul_le_mul_of_nonneg_left (fanInd_tri_le _ _ _ _ _ _) (hΓ.1 ω)
            _ = mS * mT := h3 k l hkl
      have step : (∑ k : Fin t, ∑ l : Fin t,
            (∑ ω, Γ ω * ((fanInd root ω * fanInd (S k) ω * fanInd (T k) ω)
              * (fanInd root ω * fanInd (S l) ω * fanInd (T l) ω))))
          ≤ ∑ k : Fin t, ∑ l : Fin t, (if k = l then z else mS * mT) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => bound k l
      have final : (∑ k : Fin t, ∑ l : Fin t, (if k = l then z else mS * mT))
          = (t : ℝ) * z + ((t : ℝ) * t - t) * (mS * mT) := by
        have inner2 : ∀ k : Fin t, (∑ l : Fin t, if k = l then z else mS * mT)
            = (t : ℝ) * (mS * mT) + z - mS * mT := by
          intro k
          have e : ∀ l : Fin t, (if k = l then z else mS * mT)
              = mS * mT + (if k = l then z - mS * mT else 0) := by
            intro l; by_cases hkl : k = l <;> simp [hkl]
          simp only [e]
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Finset.sum_ite_eq]
          simp only [Finset.mem_univ, ite_true]
          ring
        simp only [inner2]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [final] at step
      exact step
    have hcs2 : ((t : ℝ) * z) ^ 2 ≤ mR * ((t : ℝ) * z + ((t : ℝ) * t - t) * (mS * mT)) :=
      le_trans hcs (mul_le_mul_of_nonneg_left hQ hmR)
    have hfinal : (t : ℝ) * ((t : ℝ) * (z ^ 2 - mR * mS * mT))
        ≤ (t : ℝ) * (mR * z - mR * mS * mT) := by nlinarith [hcs2]
    exact le_of_mul_le_mul_left hfinal htR

/-! ### The three rootings -/

private lemma fan_bounds_A {t : ℕ} (ht : 1 ≤ t) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible t P) :
    (t : ℝ) * atom000 P ≤ margA P + (t.choose 2 : ℝ) * (margB P * margC P) ∧
      (t : ℝ) * (atom000 P ^ 2 - margA P * margB P * margC P)
        ≤ margA P * atom000 P - margA P * margB P * margC P := by
  obtain ⟨Γ, hΓ, hs, hd⟩ := h
  have i0 : Fin t := ⟨0, ht⟩
  refine fan_abstract ht hΓ (root := Obs.A i0 i0) (S := fun k => Obs.B i0 k)
    (T := fun k => Obs.C i0 k) (z := atom000 P) (mR := margA P) (mS := margB P) (mT := margC P)
    ?_ ?_ ?_
  · rw [← margP_A]
    exact expect_single hP hd hs Party.A i0 (1, 1, 1) _ (by simp [obsDiag, Obs.perm])
  · intro k
    exact expect_triple hP hd hs i0 (1, 1, Equiv.swap k i0) _ _ _
      (by simp [Obs.perm]) (by simp [Obs.perm]) (by simp [Obs.perm])
  · intro k l hkl
    rw [← margP_B, ← margP_C]
    exact expect_pair hP hd hs Party.B Party.C hkl (Equiv.swap k i0, Equiv.swap l i0, 1) _ _
      (by simp [obsDiag, Obs.perm]) (by simp [obsDiag, Obs.perm])

private lemma fan_bound_B {t : ℕ} (ht : 1 ≤ t) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible t P) :
    (t : ℝ) * (atom000 P ^ 2 - margA P * margB P * margC P)
      ≤ margB P * atom000 P - margA P * margB P * margC P := by
  obtain ⟨Γ, hΓ, hs, hd⟩ := h
  have i0 : Fin t := ⟨0, ht⟩
  have key := (fan_abstract ht hΓ (root := Obs.B i0 i0) (S := fun j => Obs.A i0 j)
    (T := fun j => Obs.C j i0) (z := atom000 P) (mR := margB P) (mS := margA P)
    (mT := margC P) ?_ ?_ ?_).2
  · have e : margB P * margA P * margC P = margA P * margB P * margC P := by ring
    rw [e] at key
    exact key
  · rw [← margP_B]
    exact expect_single hP hd hs Party.B i0 (1, 1, 1) _ (by simp [obsDiag, Obs.perm])
  · intro j
    have := expect_triple hP hd hs i0 (1, Equiv.swap j i0, 1)
      (Obs.A i0 j) (Obs.B i0 i0) (Obs.C j i0)
      (by simp [Obs.perm]) (by simp [Obs.perm]) (by simp [Obs.perm])
    rw [← this]
    exact Finset.sum_congr rfl fun ω _ => by ring
  · intro j j' hjj
    rw [← margP_A, ← margP_C]
    exact expect_pair hP hd hs Party.A Party.C hjj (Equiv.swap j i0, 1, Equiv.swap j' i0) _ _
      (by simp [obsDiag, Obs.perm]) (by simp [obsDiag, Obs.perm])

private lemma fan_bound_C {t : ℕ} (ht : 1 ≤ t) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible t P) :
    (t : ℝ) * (atom000 P ^ 2 - margA P * margB P * margC P)
      ≤ margC P * atom000 P - margA P * margB P * margC P := by
  obtain ⟨Γ, hΓ, hs, hd⟩ := h
  have i0 : Fin t := ⟨0, ht⟩
  have key := (fan_abstract ht hΓ (root := Obs.C i0 i0) (S := fun i => Obs.A i i0)
    (T := fun i => Obs.B i i0) (z := atom000 P) (mR := margC P) (mS := margA P)
    (mT := margB P) ?_ ?_ ?_).2
  · have e : margC P * margA P * margB P = margA P * margB P * margC P := by ring
    rw [e] at key
    exact key
  · rw [← margP_C]
    exact expect_single hP hd hs Party.C i0 (1, 1, 1) _ (by simp [obsDiag, Obs.perm])
  · intro i
    have := expect_triple hP hd hs i0 (Equiv.swap i i0, 1, 1)
      (Obs.A i i0) (Obs.B i i0) (Obs.C i0 i0)
      (by simp [Obs.perm]) (by simp [Obs.perm]) (by simp [Obs.perm])
    rw [← this]
    exact Finset.sum_congr rfl fun ω _ => by ring
  · intro i i' hii
    rw [← margP_A, ← margP_B]
    exact expect_pair hP hd hs Party.A Party.B hii (1, Equiv.swap i i0, Equiv.swap i' i0) _ _
      (by simp [obsDiag, Obs.perm]) (by simp [obsDiag, Obs.perm])

/-- Paper Theorem 5.11 (`thm:fan`), first inequality: if `P ∈ I^NW_t` then
`t z ≤ a + C(t,2) b c`, where `a = P_A(0)`, `b = P_B(0)`, `c = P_C(0)`, `z = P(000)`. -/
theorem fan_first (t : ℕ) (ht : 1 ≤ t) {P : ThreeBit → ℝ} (hP : IsLaw P) (h : NWFeasible t P) :
    (t : ℝ) * atom000 P ≤ margA P + (t.choose 2 : ℝ) * (margB P * margC P) :=
  (fan_bounds_A ht hP h).1

/-- Paper Theorem 5.11 (`thm:fan`), second inequality: if `P ∈ I^NW_t` then
`t (z² - abc) ≤ az - abc`. -/
theorem fan_second (t : ℕ) (ht : 1 ≤ t) {P : ThreeBit → ℝ} (hP : IsLaw P) (h : NWFeasible t P) :
    (t : ℝ) * (atom000 P ^ 2 - margA P * margB P * margC P)
      ≤ margA P * atom000 P - margA P * margB P * margC P :=
  (fan_bounds_A ht hP h).2

/-- Any order past the rooted fan ratio rejects. -/
private lemma not_nwFeasible_of_lt {P : ThreeBit → ℝ} (hP : IsLaw P) (T : ℕ) (hT : 1 ≤ T)
    (hgt : atom000 P * min (margA P) (min (margB P) (margC P)) - margA P * margB P * margC P
        < (T : ℝ) * (atom000 P ^ 2 - margA P * margB P * margC P)) :
    ¬ NWFeasible T P := by
  intro hfeas
  have hA := (fan_bounds_A hT hP hfeas).2
  have hB := fan_bound_B hT hP hfeas
  have hC := fan_bound_C hT hP hfeas
  rcases min_choice (margA P) (min (margB P) (margC P)) with hm | hm
  · rw [hm] at hgt; nlinarith [hA]
  · rcases min_choice (margB P) (margC P) with hm' | hm'
    · rw [hm, hm'] at hgt; nlinarith [hB]
    · rw [hm, hm'] at hgt; nlinarith [hC]

/-- Paper Theorem 5.11 (`thm:fan`), rejecting-order corollary (eq:fan-order): a Finner
violation `z² > abc` gives the explicit first rejecting order
`t_min^NW(P) ≤ ⌊(z min{a,b,c} - abc)/(z² - abc)⌋ + 1`.

The floor is `Nat.floor`; the paper's ratio is at least `1`, so the two agree. -/
theorem tminNW_le_of_finner_violation {P : ThreeBit → ℝ} (hP : IsLaw P)
    (hv : margA P * margB P * margC P < atom000 P ^ 2) :
    tminNW P
      ≤ ⌊(atom000 P * min (margA P) (min (margB P) (margC P))
            - margA P * margB P * margC P)
          / (atom000 P ^ 2 - margA P * margB P * margC P)⌋₊ + 1 := by
  have hD0 : 0 < atom000 P ^ 2 - margA P * margB P * margC P := by linarith
  simp only [tminNW]
  refine Nat.sInf_le ⟨Nat.le_add_left 1 _, not_nwFeasible_of_lt hP _ (Nat.le_add_left 1 _) ?_⟩
  rw [← div_lt_iff₀ hD0]
  push_cast
  exact Nat.lt_floor_add_one _

/-- Paper Theorem 5.11 (`thm:fan`), rejecting-order corollary for the ancestral-independence
hierarchy: the smaller feasible sets reject no later. -/
theorem tminAI_le_of_finner_violation {P : ThreeBit → ℝ} (hP : IsLaw P)
    (hv : margA P * margB P * margC P < atom000 P ^ 2) :
    tminAI P
      ≤ ⌊(atom000 P * min (margA P) (min (margB P) (margC P))
            - margA P * margB P * margC P)
          / (atom000 P ^ 2 - margA P * margB P * margC P)⌋₊ + 1 := by
  have hD0 : 0 < atom000 P ^ 2 - margA P * margB P * margC P := by linarith
  simp only [tminAI]
  refine Nat.sInf_le ⟨Nat.le_add_left 1 _, fun hai =>
    not_nwFeasible_of_lt hP _ (Nat.le_add_left 1 _) ?_ (nwFeasible_of_aiFeasible hai)⟩
  rw [← div_lt_iff₀ hD0]
  push_cast
  exact Nat.lt_floor_add_one _

/-! ## Proposition 5.12: no uniformly divergent distance lower bound -/

/-- The order-one assignments are exactly the three-bit outcomes. -/
private def assignOneEquiv : Assign 1 ≃ ThreeBit where
  toFun ω := readTriangle 0 0 0 ω
  invFun w := fun v => match v with
    | Obs.A _ _ => w.1
    | Obs.B _ _ => w.2.1
    | Obs.C _ _ => w.2.2
  left_inv ω := by
    funext v
    cases v with
    | A i j => rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; rfl
    | B i k => rw [Subsingleton.elim i 0, Subsingleton.elim k 0]; rfl
    | C j k => rw [Subsingleton.elim j 0, Subsingleton.elim k 0]; rfl
  right_inv w := rfl

private lemma obs_one_read (ω : Assign 1) (v : Obs 1) :
    partyBit v.party (readTriangle 0 0 0 ω) = ω v := by
  cases v with
  | A i j => rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; rfl
  | B i k => rw [Subsingleton.elim i 0, Subsingleton.elim k 0]; rfl
  | C j k => rw [Subsingleton.elim j 0, Subsingleton.elim k 0]; rfl

private lemma restrict_one (S : Finset (Obs 1)) (ω : Assign 1) :
    restrictAssign S ω = partyRead S (assignOneEquiv ω) :=
  funext fun v => (obs_one_read ω v.1).symm

private lemma pushforward_equiv {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (e : α ≃ β) (P : β → ℝ) (G : β → γ) :
    pushforward (fun a => P (e a)) (fun a => G (e a)) = pushforward P G := by
  funext c
  simp only [pushforward]
  exact Fintype.sum_equiv e _ _ (fun a => rfl)

private lemma obs_one_not_disjoint (u v : Obs 1) :
    ¬ Disjoint (Obs.ancestors u) (Obs.ancestors v) := by
  revert u v; decide

private lemma symmetric_one {P : ThreeBit → ℝ} :
    SymmetricLaw 1 (fun ω => P (assignOneEquiv ω)) := by
  intro π ω
  have e1 : π.1 0 = (0 : Fin 1) := Subsingleton.elim _ _
  have e2 : π.2.1 0 = (0 : Fin 1) := Subsingleton.elim _ _
  have e3 : π.2.2 0 = (0 : Fin 1) := Subsingleton.elim _ _
  change P (readTriangle 0 0 0 (relabel π ω)) = P (readTriangle 0 0 0 ω)
  simp only [readTriangle, relabel, Obs.perm, e1, e2, e3]

private lemma isLaw_one {P : ThreeBit → ℝ} (hP : IsLaw P) :
    IsLaw (fun ω : Assign 1 => P (assignOneEquiv ω)) := by
  refine ⟨fun ω => hP.1 _, ?_⟩
  rw [Equiv.sum_comp assignOneEquiv P]
  exact hP.2

private lemma diagonal_one {P : ThreeBit → ℝ} :
    pushforward (fun ω : Assign 1 => P (assignOneEquiv ω)) readDiagonal = tensorPow 1 P := by
  funext v
  change ∑ ω : Assign 1, (if readDiagonal ω = v then P (assignOneEquiv ω) else 0) = tensorPow 1 P v
  have hcond : ∀ ω : Assign 1, (readDiagonal ω = v) ↔ (assignOneEquiv ω = v 0) := by
    intro ω
    constructor
    · intro h; rw [← h]; rfl
    · intro h; funext l; rw [Subsingleton.elim l 0]; exact h
  have hstep : ∀ ω : Assign 1, (if readDiagonal ω = v then P (assignOneEquiv ω) else 0)
      = (if assignOneEquiv ω = v 0 then P (assignOneEquiv ω) else 0) := by
    intro ω; simp only [hcond ω]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω),
    Fintype.sum_equiv assignOneEquiv
      (fun ω => if assignOneEquiv ω = v 0 then P (assignOneEquiv ω) else 0)
      (fun w => if w = v 0 then P w else 0) (fun ω => rfl)]
  simp [tensorPow]

/-- Paper Proposition 5.12 (`prop:Rp`): order one is passed by every law. -/
theorem nwFeasible_one {P : ThreeBit → ℝ} (hP : IsLaw P) : NWFeasible 1 P :=
  ⟨fun ω => P (assignOneEquiv ω), isLaw_one hP, symmetric_one, diagonal_one⟩

/-- Order one is passed by every law for the ancestral-independence hierarchy as well. -/
theorem aiFeasible_one {P : ThreeBit → ℝ} (hP : IsLaw P) : AIFeasible 1 P := by
  have hempty : ∀ (s : Finset (Obs 1)), s = ∅ → ∀ f g : (↥s → Bool), f = g := by
    rintro s rfl f g
    funext x
    exact absurd x.2 (Finset.notMem_empty _)
  have hIM : InjectableMarginals 1 (fun ω => P (assignOneEquiv ω)) P := by
    intro S _
    rw [show restrictAssign S = fun ω => partyRead S (assignOneEquiv ω) from
      funext (restrict_one S)]
    exact pushforward_equiv assignOneEquiv P (partyRead S)
  refine ⟨fun ω => P (assignOneEquiv ω), isLaw_one hP, symmetric_one, diagonal_one, hIM, ?_⟩
  intro n S hinj hind
  funext φ
  have hone : ∀ m : Fin n, S m = ∅ → pushforward P (partyRead (S m)) (φ m) = 1 := by
    intro m hm
    have e : ∀ w : ThreeBit, (if partyRead (S m) w = φ m then P w else 0) = P w := by
      intro w; rw [ite_eq_left (hempty (S m) hm _ _)]
    simp only [pushforward, e]
    exact hP.2
  have hshare : ∀ m m' : Fin n, m ≠ m' → S m = ∅ ∨ S m' = ∅ := by
    intro m m' hne
    by_contra hc
    push Not at hc
    obtain ⟨u, hu⟩ := hc.1
    obtain ⟨u', hu'⟩ := hc.2
    obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.mp (obs_one_not_disjoint u u')
    exact (Finset.disjoint_left.mp (hind m m' hne)
      (Finset.mem_biUnion.mpr ⟨u, hu, hx1⟩)) (Finset.mem_biUnion.mpr ⟨u', hu', hx2⟩)
  by_cases hall : ∀ m, S m = ∅
  · have h1 : ∀ ω : Assign 1, (fun m => restrictAssign (S m) ω) = φ := fun ω =>
      funext fun m => hempty (S m) (hall m) _ _
    have e : ∀ ω : Assign 1,
        (if (fun m => restrictAssign (S m) ω) = φ then P (assignOneEquiv ω) else 0)
          = P (assignOneEquiv ω) := fun ω => ite_eq_left (h1 ω)
    change (∑ ω : Assign 1,
        (if (fun m => restrictAssign (S m) ω) = φ then P (assignOneEquiv ω) else 0)) = _
    rw [Finset.sum_congr rfl (fun ω _ => e ω), Equiv.sum_comp assignOneEquiv P, hP.2]
    exact (Finset.prod_eq_one (fun m _ => hone m (hall m))).symm
  · push Not at hall
    obtain ⟨m₀, hm₀⟩ := hall
    have hother : ∀ m, m ≠ m₀ → S m = ∅ := fun m hm =>
      (hshare m m₀ hm).resolve_right (Finset.nonempty_iff_ne_empty.mp hm₀)
    have hcond : ∀ ω : Assign 1,
        ((fun m => restrictAssign (S m) ω) = φ) ↔ (restrictAssign (S m₀) ω = φ m₀) := by
      intro ω
      constructor
      · intro h; exact congrFun h m₀
      · intro h
        funext m
        by_cases hm : m = m₀
        · subst hm; exact h
        · exact hempty (S m) (hother m hm) _ _
    have hL : (∑ ω : Assign 1,
          (if (fun m => restrictAssign (S m) ω) = φ then P (assignOneEquiv ω) else 0))
        = ∑ ω : Assign 1,
            (if restrictAssign (S m₀) ω = φ m₀ then P (assignOneEquiv ω) else 0) :=
      Finset.sum_congr rfl fun ω _ => by simp only [hcond ω]
    change (∑ ω : Assign 1,
        (if (fun m => restrictAssign (S m) ω) = φ then P (assignOneEquiv ω) else 0)) = _
    rw [hL]
    change pushforward (fun ω : Assign 1 => P (assignOneEquiv ω)) (restrictAssign (S m₀)) (φ m₀) = _
    rw [congrFun (hIM (S m₀) (hinj m₀)) (φ m₀)]
    exact (Finset.prod_eq_single_of_mem m₀ (Finset.mem_univ _)
      (fun m _ hm => hone m (hother m hm))).symm

/-- Paper Proposition 5.12 (`prop:Rp`): `R_p` fails the first fan inequality at order two,
which reads `2p ≤ p + p²`. -/
private lemma Rlaw_atom000 (p : ℝ) : atom000 (Rlaw p) = p := by
  simp [atom000, Rlaw]

private lemma Rlaw_margA (p : ℝ) : margA (Rlaw p) = p := by
  simp [margA, Rlaw]

private lemma Rlaw_margB (p : ℝ) : margB (Rlaw p) = p := by
  simp [margB, Rlaw]

private lemma Rlaw_margC (p : ℝ) : margC (Rlaw p) = p := by
  simp [margC, Rlaw]

theorem Rlaw_not_nwFeasible_two {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    ¬ NWFeasible 2 (Rlaw p) := by
  intro hf
  have hlaw : IsLaw (Rlaw p) := Rlaw_isLaw h0.le h1.le
  have h := fan_first 2 (by norm_num) hlaw hf
  rw [Rlaw_atom000, Rlaw_margA, Rlaw_margB, Rlaw_margC] at h
  norm_num at h
  nlinarith [h]

/-- Paper Proposition 5.12 (`prop:Rp`): `t_min^NW(R_p) = 2` for every `0 < p < 1`, while
`R_p → δ_{111} ∈ C_tri` as `p ↓ 0`. Hence no lower bound of the form
`t_min^H(P) ≥ c d_TV(P, C_tri)^{-α}` can hold for all incompatible `P`. -/
theorem Rlaw_tminNW {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : tminNW (Rlaw p) = 2 := by
  have hlaw : IsLaw (Rlaw p) := Rlaw_isLaw h0.le h1.le
  have h2 : (2 : ℕ) ∈ {t : ℕ | 1 ≤ t ∧ ¬ NWFeasible t (Rlaw p)} :=
    ⟨by norm_num, Rlaw_not_nwFeasible_two h0 h1⟩
  have hle : tminNW (Rlaw p) ≤ 2 := Nat.sInf_le h2
  have hmem : tminNW (Rlaw p) ∈ {t : ℕ | 1 ≤ t ∧ ¬ NWFeasible t (Rlaw p)} :=
    Nat.sInf_mem ⟨2, h2⟩
  obtain ⟨hge, hnf⟩ := hmem
  have hne1 : tminNW (Rlaw p) ≠ 1 := by
    intro h
    rw [h] at hnf
    exact hnf (nwFeasible_one hlaw)
  omega

/-- Paper Proposition 5.12 (`prop:Rp`) for the ancestral-independence hierarchy. -/
theorem Rlaw_tminAI {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : tminAI (Rlaw p) = 2 := by
  have hlaw : IsLaw (Rlaw p) := Rlaw_isLaw h0.le h1.le
  have h2 : (2 : ℕ) ∈ {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Rlaw p)} :=
    ⟨by norm_num, fun hai => Rlaw_not_nwFeasible_two h0 h1 (nwFeasible_of_aiFeasible hai)⟩
  have hle : tminAI (Rlaw p) ≤ 2 := Nat.sInf_le h2
  have hmem : tminAI (Rlaw p) ∈ {t : ℕ | 1 ≤ t ∧ ¬ AIFeasible t (Rlaw p)} :=
    Nat.sInf_mem ⟨2, h2⟩
  obtain ⟨hge, hnf⟩ := hmem
  have hne1 : tminAI (Rlaw p) ≠ 1 := by
    intro h
    rw [h] at hnf
    exact hnf (aiFeasible_one hlaw)
  omega

end

end TriangleInflation
