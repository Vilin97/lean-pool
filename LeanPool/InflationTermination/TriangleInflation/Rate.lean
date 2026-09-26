/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation.Exponent

/-!
# The distance rate of the Navascués–Wolfe hierarchy

The theorem `rate_triangle` proves the binary-triangle bound with coefficient
`1 - (1 - 1/n)³` by separating copied-triangle pairs according to shared source indices.
This is weaker than the coefficient `1/n` in manuscript Corollary 6.1 (`prop:promised`,
`eq:nw-rate`) at revision `2aa1f05ce932fdeef3896c83d287abd77cd8befb`.
`ConvexOrder.rate_triangle_sharp` proves the latter estimate for the binary triangle.

Both statements produce a compatible law at the asserted squared Euclidean distance.
The general correlation-scenario result and the rejecting-order bounds expressed using
the infimum distance to the compatible set are beyond the scope of this module.
-/

@[expose] public section

namespace TriangleInflation

open Finset

noncomputable
section

/-- The squared Euclidean norm of a weight function on three bits. -/
def sqNorm (w : ThreeBit → ℝ) : ℝ := ∑ x : ThreeBit, w x ^ 2

/-! ## Auxiliary facts

The proof of `rate_triangle` uses a collision-counting estimate with three source types.
The facts it needs about product laws, about the symmetry group of the inflation, and about
the empirical law of a random copied triangle are not stated in the imported files, so they
are proved here privately. -/

/-! ### Marginals of a product law -/

/-- The total mass of a product weight on a pi type factors. -/
private theorem sum_prod_pi {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (f : ι → α → ℝ) : ∑ v : ι → α, ∏ i, f i (v i) = ∏ i, ∑ a : α, f i a := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- One-coordinate marginal of a tensor power. -/
private theorem tensorPow_marg_one {n : ℕ} {P : ThreeBit → ℝ} (hP : ∑ w, P w = 1)
    (l : Fin n) (φ : ThreeBit → ℝ) :
    ∑ v : Fin n → ThreeBit, tensorPow n P v * φ (v l) = ∑ w, P w * φ w := by
  have hg : ∀ v : Fin n → ThreeBit,
      (∏ i, (P (v i) * (if i = l then φ (v i) else 1))) = tensorPow n P v * φ (v l) := by
    intro v
    rw [Finset.prod_mul_distrib]
    congr 1
    simp
  have hsum : ∀ i : Fin n, (∑ a : ThreeBit, P a * (if i = l then φ a else 1))
      = (if i = l then (∑ w, P w * φ w) else 1) := by
    intro i
    by_cases hi : i = l <;> simp [hi, hP]
  calc ∑ v : Fin n → ThreeBit, tensorPow n P v * φ (v l)
      = ∑ v : Fin n → ThreeBit, ∏ i, (P (v i) * (if i = l then φ (v i) else 1)) :=
        (Finset.sum_congr rfl fun v _ => hg v).symm
    _ = ∏ i : Fin n, ∑ a : ThreeBit, P a * (if i = l then φ a else 1) :=
        sum_prod_pi (fun i a => P a * (if i = l then φ a else 1))
    _ = ∑ w, P w * φ w := by
        rw [Finset.prod_congr rfl fun i _ => hsum i]
        simp

/-- Two-coordinate marginal of a tensor power at two distinct coordinates. -/
private theorem tensorPow_marg_two {n : ℕ} {P : ThreeBit → ℝ} (hP : ∑ w, P w = 1)
    {l m : Fin n} (hlm : l ≠ m) (φ ψ : ThreeBit → ℝ) :
    ∑ v : Fin n → ThreeBit, tensorPow n P v * φ (v l) * ψ (v m)
      = (∑ w, P w * φ w) * (∑ w, P w * ψ w) := by
  have hml : ¬ (m = l) := fun hh => hlm hh.symm
  have hg : ∀ v : Fin n → ThreeBit,
      (∏ i, (P (v i) * ((if i = l then φ (v i) else 1) * (if i = m then ψ (v i) else 1))))
        = tensorPow n P v * φ (v l) * ψ (v m) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_assoc]
    congr 1
    congr 1 <;> simp
  have hsum : ∀ i : Fin n,
      (∑ a : ThreeBit, P a * ((if i = l then φ a else 1) * (if i = m then ψ a else 1)))
        = (if i = l then (∑ w, P w * φ w) else 1) * (if i = m then (∑ w, P w * ψ w) else 1) := by
    intro i
    by_cases hi : i = l
    · subst hi
      simp only [ite_eq_right hlm, mul_one]
      simp
    · by_cases hj : i = m
      · subst hj
        simp only [ite_eq_right hi, one_mul]
        simp
      · simp [hi, hj, hP]
  calc ∑ v : Fin n → ThreeBit, tensorPow n P v * φ (v l) * ψ (v m)
      = ∑ v : Fin n → ThreeBit,
          ∏ i, (P (v i) * ((if i = l then φ (v i) else 1) * (if i = m then ψ (v i) else 1))) :=
        (Finset.sum_congr rfl fun v _ => hg v).symm
    _ = ∏ i : Fin n, ∑ a : ThreeBit,
          P a * ((if i = l then φ a else 1) * (if i = m then ψ a else 1)) :=
        sum_prod_pi (fun i a => P a * ((if i = l then φ a else 1) * (if i = m then ψ a else 1)))
    _ = (∑ w, P w * φ w) * (∑ w, P w * ψ w) := by
        rw [Finset.prod_congr rfl fun i _ => hsum i, Finset.prod_mul_distrib]
        congr 1 <;> simp

/-- The expectation of a function of a pushed-forward variable. -/
private theorem sum_mul_comp {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) (φ : β → ℝ) :
    ∑ a : α, w a * φ (F a) = ∑ b : β, pushforward w F b * φ b := by
  simp only [pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Finset.sum_ite_eq, ite_mul]

/-- Two indicators of a common value multiply to the indicator of agreement. -/
theorem sum_ind_eq (a b : ThreeBit) :
    (∑ c : ThreeBit, (if a = c then (1:ℝ) else 0) * (if b = c then (1:ℝ) else 0))
      = if a = b then (1:ℝ) else 0 := by
  rcases eq_or_ne a b with rfl | hne
  · simp
  · rw [ite_eq_right hne]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases eq_or_ne a c with rfl | h
    · simp [Ne.symm hne]
    · simp [h]

/-! ### The symmetry group of the inflation -/

section Sym
variable {t : ℕ}

/-- The componentwise inverse of an index-permutation triple. -/
private def permInv (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) :
    Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t) := (π.1⁻¹, π.2.1⁻¹, π.2.2⁻¹)

private theorem relabel_permInv (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (ω : Assign t) : relabel (permInv π) (relabel π ω) = ω := by
  funext v
  cases v <;> simp [relabel, Obs.perm, permInv]

private theorem relabel_permInv' (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (ω : Assign t) : relabel π (relabel (permInv π) ω) = ω := by
  funext v
  cases v <;> simp [relabel, Obs.perm, permInv]

/-- Relabelling is a bijection of assignments, so sums over assignments are invariant. -/
private theorem sum_relabel (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t))
    (F : Assign t → ℝ) : ∑ ω : Assign t, F (relabel π ω) = ∑ ω : Assign t, F ω := by
  refine Fintype.sum_bijective (relabel π) ?_ _ _ (fun _ => rfl)
  exact Function.bijective_iff_has_inverse.2
    ⟨relabel (permInv π), relabel_permInv π, relabel_permInv' π⟩

/-- The defining invariance of a symmetric law, applied inside an expectation. -/
theorem sym_sum {Γ : Assign t → ℝ} (hsym : SymmetricLaw t Γ)
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (F : Assign t → ℝ) :
    ∑ ω : Assign t, Γ ω * F (relabel π ω) = ∑ ω : Assign t, Γ ω * F ω := by
  calc ∑ ω : Assign t, Γ ω * F (relabel π ω)
      = ∑ ω : Assign t, Γ (relabel π ω) * F (relabel π ω) :=
        Finset.sum_congr rfl fun ω _ => by rw [hsym]
    _ = ∑ ω : Assign t, Γ ω * F ω := sum_relabel π (fun ω => Γ ω * F ω)

/-- Relabelling moves the copied triangle `Δ_{ijk}` to `Δ_{σ_X i, σ_Z j, σ_Y k}`. -/
private theorem readTriangle_relabel
    (π : Equiv.Perm (Fin t) × Equiv.Perm (Fin t) × Equiv.Perm (Fin t)) (i j k : Fin t)
    (ω : Assign t) :
    readTriangle i j k (relabel π ω) = readTriangle (π.1 i) (π.2.1 j) (π.2.2 k) ω := rfl

/-- A permutation of `Fin t` carrying a given pair of distinct points to another. -/
private theorem exists_perm_two {a b c d : Fin t} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin t), σ a = c ∧ σ b = d := by
  refine ⟨(Equiv.swap a c).trans (Equiv.swap ((Equiv.swap a c) b) d), ?_, ?_⟩
  · have h1 : (Equiv.swap a c) b ≠ c := by
      intro hh
      refine hab ((Equiv.swap a c).injective ?_)
      rw [hh, Equiv.swap_apply_left]
    simp only [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) hcd
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

end Sym

/-! ### The law of one and of two copied triangles -/

/-- Every copied triangle of a Navascués–Wolfe witness has the law `P`: the permutation
`(swap l i, swap l j, swap l k)` carries the diagonal triangle `Δ_{lll}` to `Δ_{ijk}`. -/
private theorem marg_one {n : ℕ} (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    {Γ : Assign n → ℝ} (hsym : SymmetricLaw n Γ)
    (hdiag : pushforward Γ readDiagonal = tensorPow n P) (i j k : Fin n) (w : ThreeBit) :
    ∑ ω : Assign n, Γ ω * (if readTriangle i j k ω = w then (1:ℝ) else 0) = P w := by
  set l : Fin n := ⟨0, hn⟩ with hl
  set π : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) × Equiv.Perm (Fin n) :=
    (Equiv.swap l i, Equiv.swap l j, Equiv.swap l k) with hπ
  have hstep : ∀ ω : Assign n,
      (if readTriangle l l l (relabel π ω) = w then (1:ℝ) else 0)
        = (if readTriangle i j k ω = w then (1:ℝ) else 0) := by
    intro ω
    rw [readTriangle_relabel]
    simp [hπ]
  have h1 : ∑ ω : Assign n, Γ ω * (if readTriangle i j k ω = w then (1:ℝ) else 0)
      = ∑ ω : Assign n, Γ ω * (if readTriangle l l l ω = w then (1:ℝ) else 0) := by
    rw [← sym_sum hsym π (fun ω => if readTriangle l l l ω = w then (1:ℝ) else 0)]
    exact Finset.sum_congr rfl fun ω _ => by rw [hstep ω]
  have h2 := sum_mul_comp Γ readDiagonal (fun v => if v l = w then (1:ℝ) else 0)
  rw [hdiag] at h2
  simp only [readDiagonal] at h2
  rw [h1]
  refine h2.trans ?_
  rw [tensorPow_marg_one hP.2 l (fun a => if a = w then (1:ℝ) else 0)]
  simp

/-- Two copied triangles sharing no copy index have the joint law `P ⊗ P`, so they agree
with probability `‖P‖₂²`. -/
theorem marg_two {n : ℕ} {P : ThreeBit → ℝ} (hP : IsLaw P)
    {Γ : Assign n → ℝ} (hsym : SymmetricLaw n Γ)
    (hdiag : pushforward Γ readDiagonal = tensorPow n P)
    {i j k i' j' k' : Fin n} (hi : i ≠ i') (hj : j ≠ j') (hk : k ≠ k') :
    ∑ ω : Assign n, Γ ω
        * (if readTriangle i j k ω = readTriangle i' j' k' ω then (1:ℝ) else 0) = sqNorm P := by
  obtain ⟨σX, hX1, hX2⟩ := exists_perm_two hi hi
  obtain ⟨σZ, hZ1, hZ2⟩ := exists_perm_two hi hj
  obtain ⟨σY, hY1, hY2⟩ := exists_perm_two hi hk
  set π : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) × Equiv.Perm (Fin n) := (σX, σZ, σY) with hπ
  have hstep : ∀ ω : Assign n,
      (if readTriangle i i i (relabel π ω) = readTriangle i' i' i' (relabel π ω)
        then (1:ℝ) else 0)
        = (if readTriangle i j k ω = readTriangle i' j' k' ω then (1:ℝ) else 0) := by
    intro ω
    rw [readTriangle_relabel, readTriangle_relabel]
    simp only [hπ, hX1, hZ1, hY1, hX2, hZ2, hY2]
  have h1 : ∑ ω : Assign n, Γ ω
        * (if readTriangle i j k ω = readTriangle i' j' k' ω then (1:ℝ) else 0)
      = ∑ ω : Assign n, Γ ω
        * (if readTriangle i i i ω = readTriangle i' i' i' ω then (1:ℝ) else 0) := by
    rw [← sym_sum hsym π
      (fun ω => if readTriangle i i i ω = readTriangle i' i' i' ω then (1:ℝ) else 0)]
    exact Finset.sum_congr rfl fun ω _ => by rw [hstep ω]
  have h2 := sum_mul_comp Γ readDiagonal (fun v => if v i = v i' then (1:ℝ) else 0)
  rw [hdiag] at h2
  simp only [readDiagonal] at h2
  rw [h1]
  refine h2.trans ?_
  calc ∑ v : Fin n → ThreeBit, tensorPow n P v * (if v i = v i' then (1:ℝ) else 0)
      = ∑ v : Fin n → ThreeBit, ∑ a : ThreeBit,
          tensorPow n P v * (if v i = a then (1:ℝ) else 0) * (if v i' = a then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← sum_ind_eq (v i) (v i'), Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a : ThreeBit, ∑ v : Fin n → ThreeBit,
          tensorPow n P v * (if v i = a then (1:ℝ) else 0) * (if v i' = a then (1:ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ a : ThreeBit, (∑ w, P w * (if w = a then (1:ℝ) else 0))
          * (∑ w, P w * (if w = a then (1:ℝ) else 0)) :=
        Finset.sum_congr rfl fun a _ => tensorPow_marg_two hP.2 hi
          (fun c => if c = a then (1:ℝ) else 0) (fun c => if c = a then (1:ℝ) else 0)
    _ = sqNorm P := by simp [sqNorm, sq]

/-! ### The empirical law of a random copied triangle -/

/-- The number of copied triangles that a deterministic assignment reads as `w`. -/
def triCount {n : ℕ} (ω : Assign n) (w : ThreeBit) : ℝ :=
  ∑ c : Cell n, if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0

/-- The empirical law of the `n³` copied triangles of a deterministic assignment: sample the
three copy indices uniformly and independently, and output the three bits that the
assignment gives to the corresponding copied triangle. This is the law `q_ω` of the proof of
paper Corollary 6.1. -/
def qLaw (n : ℕ) (ω : Assign n) : ThreeBit → ℝ := fun w => triCount ω w / (n : ℝ) ^ 3

private theorem triCount_nonneg {n : ℕ} (ω : Assign n) (w : ThreeBit) : 0 ≤ triCount ω w :=
  Finset.sum_nonneg fun c _ => by positivity

private theorem sum_triCount {n : ℕ} (ω : Assign n) : ∑ w, triCount ω w = (n : ℝ) ^ 3 := by
  simp only [triCount]
  rw [Finset.sum_comm]
  have h : ∀ c : Cell n,
      (∑ w : ThreeBit, if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0) = 1 := by
    intro c
    simp
  rw [Finset.sum_congr rfl fun c _ => h c]
  simp [Finset.card_univ, Cell]
  ring

/-- The squared masses of the empirical law count the ordered pairs of copied triangles that
the assignment reads alike. -/
private theorem sum_triCount_sq {n : ℕ} (ω : Assign n) :
    ∑ w : ThreeBit, triCount ω w ^ 2
      = ∑ p : Cell n × Cell n,
          (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
            then (1:ℝ) else 0) := by
  have hsq : ∀ w : ThreeBit, triCount ω w ^ 2
      = ∑ c : Cell n, ∑ c' : Cell n,
          (if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0)
            * (if readTriangle c'.1 c'.2.1 c'.2.2 ω = w then (1:ℝ) else 0) := by
    intro w
    rw [sq, triCount, Finset.sum_mul_sum]
  calc ∑ w : ThreeBit, triCount ω w ^ 2
      = ∑ w : ThreeBit, ∑ c : Cell n, ∑ c' : Cell n,
          (if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0)
            * (if readTriangle c'.1 c'.2.1 c'.2.2 ω = w then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun w _ => hsq w
    _ = ∑ c : Cell n, ∑ w : ThreeBit, ∑ c' : Cell n,
          (if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0)
            * (if readTriangle c'.1 c'.2.1 c'.2.2 ω = w then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ c : Cell n, ∑ c' : Cell n, ∑ w : ThreeBit,
          (if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0)
            * (if readTriangle c'.1 c'.2.1 c'.2.2 ω = w then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : Cell n, ∑ c' : Cell n,
          (if readTriangle c.1 c.2.1 c.2.2 ω = readTriangle c'.1 c'.2.1 c'.2.2 ω
            then (1:ℝ) else 0) :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ =>
          sum_ind_eq (readTriangle c.1 c.2.1 c.2.2 ω) (readTriangle c'.1 c'.2.1 c'.2.2 ω)
    _ = ∑ p : Cell n × Cell n,
          (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
            then (1:ℝ) else 0) :=
        (Fintype.sum_prod_type (fun p : Cell n × Cell n =>
          if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
            then (1:ℝ) else 0)).symm

theorem qLaw_isLaw {n : ℕ} (hn : 1 ≤ n) (ω : Assign n) : IsLaw (qLaw n ω) := by
  have hn0 : (0:ℝ) < (n:ℝ) ^ 3 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  refine ⟨fun w => div_nonneg (triCount_nonneg ω w) (le_of_lt hn0), ?_⟩
  simp only [qLaw]
  rw [← Finset.sum_div, sum_triCount]
  field_simp

/-- A deterministic response: the outcome `0` has probability `1` exactly when the
assignment gives the outcome `0`. -/
private theorem respMass_det (c b : Bool) :
    respMass (if c then 0 else 1) b = if b = c then (1:ℝ) else 0 := by
  cases c <;> cases b <;> simp [respMass]

private theorem ind_triple (a1 a2 a3 b1 b2 b3 : Bool) :
    (if b1 = a1 then (1:ℝ) else 0) * (if b2 = a2 then (1:ℝ) else 0)
        * (if b3 = a3 then (1:ℝ) else 0)
      = if ((a1, a2, a3) : ThreeBit) = (b1, b2, b3) then (1:ℝ) else 0 := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    norm_num [Prod.ext_iff]

/-- The triangle model realizing `qLaw n ω`: three uniform sources on `Fin n`, one for each
source type, and deterministic responses read off `ω`. -/
private def detModel (n : ℕ) (ω : Assign n) : TriangleModel where
  X := Fin n
  Y := Fin n
  Z := Fin n
  fintypeX := inferInstance
  fintypeY := inferInstance
  fintypeZ := inferInstance
  μX := fun _ => 1 / (n : ℝ)
  μY := fun _ => 1 / (n : ℝ)
  μZ := fun _ => 1 / (n : ℝ)
  f := fun p => if ω (Obs.A p.1 p.2) then 0 else 1
  g := fun p => if ω (Obs.B p.1 p.2) then 0 else 1
  h := fun p => if ω (Obs.C p.1 p.2) then 0 else 1

private theorem detModel_valid {n : ℕ} (hn : 1 ≤ n) (ω : Assign n) : (detModel n ω).Valid := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hlaw : IsLaw (fun _ : Fin n => 1 / (n : ℝ)) := by
    refine ⟨fun _ => by positivity, ?_⟩
    simp [Finset.card_univ]
    field_simp
  refine ⟨hlaw, hlaw, hlaw, ?_, ?_, ?_⟩ <;>
    · intro p
      simp only [detModel]
      constructor <;> split <;> norm_num

private theorem detModel_law {n : ℕ} (ω : Assign n) : (detModel n ω).law = qLaw n ω := by
  funext w
  obtain ⟨w1, w2, w3⟩ := w
  have hpt : ∀ x y z : Fin n,
      (1 / (n:ℝ)) * (1 / (n:ℝ)) * (1 / (n:ℝ))
          * respMass (if ω (Obs.A x z) then 0 else 1) w1
          * respMass (if ω (Obs.B x y) then 0 else 1) w2
          * respMass (if ω (Obs.C z y) then 0 else 1) w3
        = (if readTriangle x z y ω = (w1, w2, w3) then (1:ℝ) else 0) / (n:ℝ) ^ 3 := by
    intro x y z
    rw [respMass_det, respMass_det, respMass_det,
      show readTriangle x z y ω = ((ω (Obs.A x z)), (ω (Obs.B x y)), (ω (Obs.C z y))) from rfl,
      ← ind_triple (ω (Obs.A x z)) (ω (Obs.B x y)) (ω (Obs.C z y)) w1 w2 w3]
    ring
  calc (detModel n ω).law (w1, w2, w3)
      = ∑ x : Fin n, ∑ y : Fin n, ∑ z : Fin n,
          (if readTriangle x z y ω = (w1, w2, w3) then (1:ℝ) else 0) / (n:ℝ) ^ 3 := by
        simp only [TriangleModel.law, detModel]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun z _ => hpt x y z
    _ = ∑ x : Fin n, ∑ z : Fin n, ∑ y : Fin n,
          (if readTriangle x z y ω = (w1, w2, w3) then (1:ℝ) else 0) / (n:ℝ) ^ 3 :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = qLaw n ω (w1, w2, w3) := by
        simp only [qLaw, triCount, Finset.sum_div, Fintype.sum_prod_type]

theorem qLaw_compatible {n : ℕ} (hn : 1 ≤ n) (ω : Assign n) :
    TriangleCompatible (qLaw n ω) :=
  ⟨detModel n ω, detModel_valid hn ω, detModel_law ω⟩

/-! ### Counting the pairs of copied triangles -/

/-- The number of ordered pairs of distinct copy indices. -/
theorem sum_ne_pair (n : ℕ) :
    ∑ x : Fin n × Fin n, (if x.1 ≠ x.2 then (1:ℝ) else 0) = (n:ℝ) ^ 2 - (n:ℝ) := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Fin n, (∑ b : Fin n, if a ≠ b then (1:ℝ) else 0) = (n:ℝ) - 1 := by
    intro a
    have h : ∀ b : Fin n, (if a ≠ b then (1:ℝ) else 0) = 1 - (if a = b then (1:ℝ) else 0) := by
      intro b; by_cases hb : a = b <;> simp [hb]
    rw [Finset.sum_congr rfl fun b _ => h b, Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp [Finset.card_univ]
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  simp [Finset.card_univ]
  ring

/-- A sum over three independent index pairs factors. -/
private theorem sum_triple_factor {n : ℕ} (a b c : Fin n × Fin n → ℝ) :
    ∑ q : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n), a q.1 * b q.2.1 * c q.2.2
      = (∑ x, a x) * (∑ y, b y) * (∑ z, c z) := by
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : Fin n × Fin n,
      (∑ r : (Fin n × Fin n) × (Fin n × Fin n), a x * b r.1 * c r.2)
        = a x * ((∑ y, b y) * (∑ z, c z)) := by
    intro x
    rw [Fintype.sum_prod_type,
      Finset.sum_mul_sum (Finset.univ : Finset (Fin n × Fin n))
        (Finset.univ : Finset (Fin n × Fin n)) b c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.sum_mul, ← mul_assoc]

/-- The regrouping of a pair of copied triangles into its three pairs of copy indices. -/
private def cellPairEquiv (n : ℕ) :
    (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n) ≃ Cell n × Cell n where
  toFun q := ((q.1.1, q.2.1.1, q.2.2.1), (q.1.2, q.2.1.2, q.2.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are `n³(n-1)³` ordered pairs of copied triangles sharing no copy index. -/
private theorem sum_nocol (n : ℕ) :
    ∑ p : Cell n × Cell n,
        (if p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2 then (1:ℝ) else 0)
      = ((n:ℝ) ^ 2 - (n:ℝ)) ^ 3 := by
  rw [← Equiv.sum_comp (cellPairEquiv n)]
  have hsummand : ∀ q : (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n),
      (if (cellPairEquiv n q).1.1 ≠ (cellPairEquiv n q).2.1
          ∧ (cellPairEquiv n q).1.2.1 ≠ (cellPairEquiv n q).2.2.1
          ∧ (cellPairEquiv n q).1.2.2 ≠ (cellPairEquiv n q).2.2.2 then (1:ℝ) else 0)
        = (if q.1.1 ≠ q.1.2 then (1:ℝ) else 0) * (if q.2.1.1 ≠ q.2.1.2 then (1:ℝ) else 0)
            * (if q.2.2.1 ≠ q.2.2.2 then (1:ℝ) else 0) := by
    intro q
    by_cases h1 : q.1.1 = q.1.2 <;> by_cases h2 : q.2.1.1 = q.2.1.2 <;>
      by_cases h3 : q.2.2.1 = q.2.2.2 <;> simp [cellPairEquiv, h1, h2, h3]
  rw [Finset.sum_congr rfl fun q _ => hsummand q,
    sum_triple_factor (fun x => if x.1 ≠ x.2 then (1:ℝ) else 0)
      (fun x => if x.1 ≠ x.2 then (1:ℝ) else 0) (fun x => if x.1 ≠ x.2 then (1:ℝ) else 0),
    sum_ne_pair]
  ring

/-- The number of ordered pairs of copied triangles. -/
private theorem sum_pairs_const (n : ℕ) :
    ∑ _p : Cell n × Cell n, (1:ℝ) = (n:ℝ) ^ 6 := by
  simp [Finset.card_univ, Cell]
  ring

/-! ### The two expectation identities -/

/-- The empirical law of a random copied triangle has mean `P`. -/
theorem expect_qLaw {n : ℕ} (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    {Γ : Assign n → ℝ} (hsym : SymmetricLaw n Γ)
    (hdiag : pushforward Γ readDiagonal = tensorPow n P) (w : ThreeBit) :
    ∑ ω : Assign n, Γ ω * qLaw n ω w = P w := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hcube : ((n:ℝ)) ^ 3 ≠ 0 := by positivity
  have h1 : ∑ ω : Assign n, Γ ω * qLaw n ω w
      = (∑ ω : Assign n, Γ ω * triCount ω w) / (n:ℝ) ^ 3 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun ω _ => by rw [qLaw, mul_div_assoc]
  have h2 : ∑ ω : Assign n, Γ ω * triCount ω w = (n:ℝ) ^ 3 * P w := by
    have e : ∀ ω : Assign n, Γ ω * triCount ω w
        = ∑ c : Cell n, Γ ω * (if readTriangle c.1 c.2.1 c.2.2 ω = w then (1:ℝ) else 0) := by
      intro ω
      rw [triCount, Finset.mul_sum]
    have hcard : (Finset.univ : Finset (Cell n)).card = n ^ 3 := by
      simp [Finset.card_univ, Cell]
      ring
    rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_comm,
      Finset.sum_congr rfl fun c _ => marg_one hn hP hsym hdiag c.1 c.2.1 c.2.2 w,
      Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    ring
  rw [h1, h2]
  field_simp

/-- The collision-counting estimate: with `α = (1-1/n)³` the mean squared
norm of the empirical law is at most `α‖P‖₂² + (1-α)`. The `n³(n-1)³` ordered pairs of
copied triangles sharing no copy index contribute `‖P‖₂²` each; the remaining pairs
contribute at most `1` each. -/
private theorem expect_sq_le {n : ℕ} (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    {Γ : Assign n → ℝ} (hΓ : IsLaw Γ) (hsym : SymmetricLaw n Γ)
    (hdiag : pushforward Γ readDiagonal = tensorPow n P) :
    ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2)
      ≤ 1 - (1 - sqNorm P) * (1 - 1 / (n:ℝ)) ^ 3 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h6 : (0:ℝ) < (n:ℝ) ^ 6 := by positivity
  have h1 : ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2)
      = (∑ p : Cell n × Cell n, ∑ ω : Assign n, Γ ω
          * (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
              then (1:ℝ) else 0)) / (n:ℝ) ^ 6 := by
    have ha : ∀ ω : Assign n, Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2)
        = (∑ p : Cell n × Cell n, Γ ω
            * (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
                then (1:ℝ) else 0)) / (n:ℝ) ^ 6 := by
      intro ω
      have hq : ∀ w : ThreeBit, qLaw n ω w ^ 2 = triCount ω w ^ 2 / (n:ℝ) ^ 6 := by
        intro w
        rw [qLaw, div_pow]
        ring
      rw [Finset.sum_congr rfl fun w _ => hq w, ← Finset.sum_div, sum_triCount_sq,
        Finset.sum_div, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => by rw [mul_div_assoc]
    rw [Finset.sum_congr rfl fun ω _ => ha ω, ← Finset.sum_div]
    congr 1
    exact Finset.sum_comm
  have h3 : ∀ p : Cell n × Cell n,
      (∑ ω : Assign n, Γ ω
        * (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
            then (1:ℝ) else 0))
        ≤ (if p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2 then sqNorm P else 1) := by
    intro p
    by_cases hp : p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2
    · rw [ite_eq_left hp]
      exact le_of_eq (marg_two hP hsym hdiag hp.1 hp.2.1 hp.2.2)
    · rw [ite_eq_right hp]
      calc (∑ ω : Assign n, Γ ω
              * (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
                  then (1:ℝ) else 0))
          ≤ ∑ ω : Assign n, Γ ω :=
            Finset.sum_le_sum fun ω _ =>
              mul_le_of_le_one_right (hΓ.1 ω) (by split <;> norm_num)
        _ = 1 := hΓ.2
  have h4 : ∑ p : Cell n × Cell n,
        (if p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2 then sqNorm P else 1)
      = (n:ℝ) ^ 6 - (1 - sqNorm P) * ((n:ℝ) ^ 2 - (n:ℝ)) ^ 3 := by
    have he : ∀ p : Cell n × Cell n,
        (if p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2 then sqNorm P else 1)
          = 1 - (1 - sqNorm P)
              * (if p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2 then (1:ℝ) else 0) := by
      intro p
      by_cases hp : p.1.1 ≠ p.2.1 ∧ p.1.2.1 ≠ p.2.2.1 ∧ p.1.2.2 ≠ p.2.2.2 <;> simp [hp]
    rw [Finset.sum_congr rfl fun p _ => he p, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_nocol, sum_pairs_const]
  have h5 : (∑ p : Cell n × Cell n, ∑ ω : Assign n, Γ ω
        * (if readTriangle p.1.1 p.1.2.1 p.1.2.2 ω = readTriangle p.2.1 p.2.2.1 p.2.2.2 ω
            then (1:ℝ) else 0))
      ≤ (n:ℝ) ^ 6 - (1 - sqNorm P) * ((n:ℝ) ^ 2 - (n:ℝ)) ^ 3 := by
    rw [← h4]
    exact Finset.sum_le_sum fun p _ => h3 p
  rw [h1, div_le_iff₀ h6]
  have hfin : (1 - (1 - sqNorm P) * (1 - 1 / (n:ℝ)) ^ 3) * (n:ℝ) ^ 6
      = (n:ℝ) ^ 6 - (1 - sqNorm P) * ((n:ℝ) ^ 2 - (n:ℝ)) ^ 3 := by
    field_simp
  rw [hfin]
  exact h5

/-- A weighted average is at least the minimum over the support. -/
theorem exists_le_of_weighted {α : Type*} [Fintype α] {Γ : α → ℝ}
    (h0 : ∀ a, 0 ≤ Γ a) (h1 : ∑ a, Γ a = 1) (v : α → ℝ) (c : ℝ)
    (hle : ∑ a, Γ a * v a ≤ c) : ∃ a, v a ≤ c := by
  by_contra hcon
  have hcon : ∀ a, c < v a := by
    intro a
    by_contra hle'
    exact hcon ⟨a, not_lt.1 hle'⟩
  obtain ⟨a0, -, ha0⟩ : ∃ a ∈ (Finset.univ : Finset α), (0:ℝ) < Γ a := by
    refine Finset.exists_lt_of_sum_lt (f := fun _ : α => (0:ℝ)) (g := Γ) ?_
    rw [h1]
    simp
  have hlt : ∑ a : α, Γ a * c < ∑ a : α, Γ a * v a := by
    refine Finset.sum_lt_sum
      (fun a _ => mul_le_mul_of_nonneg_left (le_of_lt (hcon a)) (h0 a)) ⟨a0, Finset.mem_univ a0, ?_⟩
    exact mul_lt_mul_of_pos_left (hcon a0) ha0
  rw [← Finset.sum_mul, h1, one_mul] at hlt
  linarith

/-! ## The distance rate -/

/-- A collision-counting distance bound for the binary triangle: if `P` is feasible at
order `n`, some triangle-compatible law `Qc` satisfies
`‖P - Qc‖₂² ≤ [1 - (1 - 1/n)³] (1 - ‖P‖₂²)`.
The sharper coefficient `1/n` of manuscript Corollary 6.1 is proved in
`rate_triangle_sharp` in `ConvexOrder.lean`. -/
theorem rate_triangle (n : ℕ) (hn : 1 ≤ n) {P : ThreeBit → ℝ} (hP : IsLaw P)
    (h : NWFeasible n P) :
    ∃ Qc : ThreeBit → ℝ, IsLaw Qc ∧ TriangleCompatible Qc ∧
      sqNorm (fun x => P x - Qc x) ≤ (1 - (1 - 1 / (n : ℝ)) ^ 3) * (1 - sqNorm P) := by
  obtain ⟨Γ, hΓ, hsym, hdiag⟩ := h
  have hB : ∑ ω : Assign n, Γ ω * (∑ w : ThreeBit, P w * qLaw n ω w) = sqNorm P := by
    have e : ∀ ω : Assign n, Γ ω * (∑ w : ThreeBit, P w * qLaw n ω w)
        = ∑ w : ThreeBit, P w * (Γ ω * qLaw n ω w) := by
      intro ω
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have e2 : ∀ w : ThreeBit, (∑ ω : Assign n, P w * (Γ ω * qLaw n ω w)) = P w * P w := by
      intro w
      rw [← Finset.mul_sum, expect_qLaw hn hP hsym hdiag w]
    rw [Finset.sum_congr rfl fun ω _ => e ω, Finset.sum_comm,
      Finset.sum_congr rfl fun w _ => e2 w]
    simp [sqNorm, sq]
  have key : ∑ ω : Assign n, Γ ω * sqNorm (fun x => P x - qLaw n ω x)
      ≤ (1 - (1 - 1 / (n : ℝ)) ^ 3) * (1 - sqNorm P) := by
    have step1 : ∀ ω : Assign n, sqNorm (fun x => P x - qLaw n ω x)
        = sqNorm P - 2 * (∑ w : ThreeBit, P w * qLaw n ω w)
          + (∑ w : ThreeBit, qLaw n ω w ^ 2) := by
      intro ω
      simp only [sqNorm]
      have e : ∀ w : ThreeBit, (P w - qLaw n ω w) ^ 2
          = P w ^ 2 - 2 * (P w * qLaw n ω w) + qLaw n ω w ^ 2 := fun w => by ring
      rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    have e1 : ∀ ω : Assign n, Γ ω * sqNorm (fun x => P x - qLaw n ω x)
        = Γ ω * sqNorm P - 2 * (Γ ω * (∑ w : ThreeBit, P w * qLaw n ω w))
          + Γ ω * (∑ w : ThreeBit, qLaw n ω w ^ 2) := by
      intro ω
      rw [step1 ω]
      ring
    rw [Finset.sum_congr rfl fun ω _ => e1 ω, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hΓ.2, one_mul, hB]
    have hC := expect_sq_le hn hP hΓ hsym hdiag
    have hring : (1 - (1 - 1 / (n : ℝ)) ^ 3) * (1 - sqNorm P)
        = 1 - sqNorm P - (1 - sqNorm P) * (1 - 1 / (n : ℝ)) ^ 3 := by ring
    rw [hring]
    linarith
  obtain ⟨ω, hω⟩ := exists_le_of_weighted hΓ.1 hΓ.2
    (fun ω => sqNorm (fun x => P x - qLaw n ω x)) _ key
  exact ⟨qLaw n ω, qLaw_isLaw hn ω, qLaw_compatible hn ω, hω⟩

end

end TriangleInflation
