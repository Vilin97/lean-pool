/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Tactic.Common
/-!
# Trigonometric polynomials

A **trigonometric polynomial** in `k` real variables is a finite `ℂ`-linear combination of the
characters `x ↦ exp (i ⟨ω, x⟩)`, where the frequency vectors `ω` range over a finite set.
These are exactly the trigonometric polynomials, and they are closed under addition,
scaling, multiplication by a single character, products, and complex conjugation — the
algebraic facts that drive the Fourier representation of the quantum kernel.

This module is quantum-free: it only knows about `ℂ`, finite sums, the real pairing
`⟨ω, x⟩ = ∑ i, ω i * x i`, and real one-variable trigonometric identities.
-/

@[expose] public section

namespace QuantumAlg

open Complex BigOperators

variable {k : ℕ}

/-- The real pairing `⟨ω, x⟩ = ∑ i, ω i * x i` of a frequency vector with a data point. -/
def freqDot (ω x : Fin k → ℝ) : ℝ := ∑ i, ω i * x i

/-- An **trigonometric polynomial** in `k` real variables: the function
`x ↦ ∑_{ω ∈ freqs} coeff ω · exp(i⟨ω, x⟩)`. The data is a finite set of
frequency vectors together with a complex coefficient at each. -/
structure TrigPolynomial (k : ℕ) where
  /-- The finite set of frequency vectors carrying nonzero (or bookkept) coefficients. -/
  freqs : Finset (Fin k → ℝ)
  /-- The complex coefficient at each frequency. -/
  coeff : (Fin k → ℝ) → ℂ

/-- Evaluate an trigonometric polynomial at a data point `x`. -/
noncomputable def TrigPolynomial.eval (f : TrigPolynomial k) (x : Fin k → ℝ) : ℂ :=
  ∑ ω ∈ f.freqs, f.coeff ω * Complex.exp (Complex.I * (freqDot ω x : ℂ))

/-- The pairing is additive in the frequency argument. -/
theorem freqDot_add (ω₁ ω₂ x : Fin k → ℝ) :
    freqDot (ω₁ + ω₂) x = freqDot ω₁ x + freqDot ω₂ x := by
  simp only [freqDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The pairing negates with the frequency argument. -/
theorem freqDot_neg (ω x : Fin k → ℝ) : freqDot (-ω) x = -freqDot ω x := by
  simp only [freqDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The pairing is additive in the data argument. -/
theorem freqDot_add_right (ω x₁ x₂ : Fin k → ℝ) :
    freqDot ω (x₁ + x₂) = freqDot ω x₁ + freqDot ω x₂ := by
  simp only [freqDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The pairing is symmetric. -/
theorem freqDot_comm (ω x : Fin k → ℝ) : freqDot ω x = freqDot x ω := by
  unfold freqDot; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The zero trigonometric polynomial (empty frequency set). -/
def TrigPolynomial.zero : TrigPolynomial k where
  freqs := ∅
  coeff := fun _ => 0

@[simp] theorem TrigPolynomial.eval_zero (x : Fin k → ℝ) :
    (TrigPolynomial.zero : TrigPolynomial k).eval x = 0 := by
  simp [TrigPolynomial.eval, TrigPolynomial.zero]

/-- Scale an trigonometric polynomial by a complex constant. -/
def TrigPolynomial.smul (c : ℂ) (f : TrigPolynomial k) : TrigPolynomial k where
  freqs := f.freqs
  coeff := fun ω => c * f.coeff ω

theorem TrigPolynomial.eval_smul (c : ℂ) (f : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.smul c).eval x = c * f.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.smul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- Sum of two trigonometric polynomials: union of frequencies, with guarded
coefficients added. -/
noncomputable def TrigPolynomial.add (f g : TrigPolynomial k) : TrigPolynomial k where
  freqs := f.freqs ∪ g.freqs
  coeff := fun ω =>
    (if ω ∈ f.freqs then f.coeff ω else 0) + (if ω ∈ g.freqs then g.coeff ω else 0)

theorem TrigPolynomial.eval_add (f g : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.add g).eval x = f.eval x + g.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_subset Finset.subset_union_left
        (fun ω _ hω => by rw [if_neg hω, zero_mul])]
    exact Finset.sum_congr rfl (fun ω hω => by rw [if_pos hω])
  · rw [← Finset.sum_subset Finset.subset_union_right
        (fun ω _ hω => by rw [if_neg hω, zero_mul])]
    exact Finset.sum_congr rfl (fun ω hω => by rw [if_pos hω])

/-- Multiply an trigonometric polynomial by the character `e^{i⟨a,x⟩}`: shifts every frequency
by `a` and leaves the coefficients (re-indexed) unchanged. -/
noncomputable def TrigPolynomial.expMul (a : Fin k → ℝ) (f : TrigPolynomial k) :
    TrigPolynomial k where
  freqs := f.freqs.image (fun ω => ω + a)
  coeff := fun ω => f.coeff (ω - a)

theorem TrigPolynomial.eval_expMul (a : Fin k → ℝ) (f : TrigPolynomial k)
    (x : Fin k → ℝ) :
    (f.expMul a).eval x = Complex.exp (Complex.I * (freqDot a x : ℂ)) * f.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.expMul]
  rw [Finset.sum_image (by intro p _ q _ h; exact add_right_cancel h), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [add_sub_cancel_right, freqDot_add]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- A finite sum of trigonometric polynomials: frequencies union over the index,
with coefficients added. -/
noncomputable def TrigPolynomial.sum {ι : Type*} (s : Finset ι)
    (F : ι → TrigPolynomial k) : TrigPolynomial k where
  freqs := s.biUnion (fun i => (F i).freqs)
  coeff := fun ω => ∑ i ∈ s, (if ω ∈ (F i).freqs then (F i).coeff ω else 0)

theorem TrigPolynomial.eval_sum {ι : Type*} (s : Finset ι) (F : ι → TrigPolynomial k)
    (x : Fin k → ℝ) :
    (TrigPolynomial.sum s F).eval x = ∑ i ∈ s, (F i).eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem (fun j => (F j).freqs) hi)
        (fun ω _ hω => by rw [if_neg hω, zero_mul])]
  exact Finset.sum_congr rfl (fun ω hω => by rw [if_pos hω])

/-- Product of two trigonometric polynomials: realised as the sum, over `f`'s frequencies, of `g`
shifted by that frequency and scaled by `f`'s coefficient. -/
noncomputable def TrigPolynomial.mul (f g : TrigPolynomial k) : TrigPolynomial k :=
  TrigPolynomial.sum f.freqs (fun ω => (g.expMul ω).smul (f.coeff ω))

theorem TrigPolynomial.eval_mul (f g : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.mul g).eval x = f.eval x * g.eval x := by
  rw [TrigPolynomial.mul, TrigPolynomial.eval_sum]
  simp only [TrigPolynomial.eval_smul, TrigPolynomial.eval_expMul]
  rw [Finset.sum_congr rfl (fun ω _ => by ring :
        ∀ ω ∈ f.freqs, f.coeff ω * (Complex.exp (Complex.I * (freqDot ω x : ℂ)) * g.eval x)
          = (f.coeff ω * Complex.exp (Complex.I * (freqDot ω x : ℂ))) * g.eval x),
    ← Finset.sum_mul]
  rfl

/-- Complex conjugate of an trigonometric polynomial: negate frequencies, conjugate coefficients. -/
noncomputable def TrigPolynomial.conj (f : TrigPolynomial k) : TrigPolynomial k where
  freqs := f.freqs.image (fun ω => -ω)
  coeff := fun ω => (starRingEnd ℂ) (f.coeff (-ω))

theorem TrigPolynomial.eval_conj (f : TrigPolynomial k) (x : Fin k → ℝ) :
    (f.conj).eval x = (starRingEnd ℂ) (f.eval x) := by
  simp only [TrigPolynomial.eval, TrigPolynomial.conj]
  rw [map_sum, Finset.sum_image (by intro p _ q _ h; exact neg_injective h)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [neg_neg, map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  rw [freqDot_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The canonical coefficient of an trigonometric polynomial at a frequency: its (guarded)
contribution. Two trigonometric polynomials with the same values have the same canonical
coefficients (`coeffAt_eq_of_eval_eq`). -/
noncomputable def TrigPolynomial.coeffAt (f : TrigPolynomial k) (ω : Fin k → ℝ) : ℂ :=
  if ω ∈ f.freqs then f.coeff ω else 0

/-- Pairing against a single scaled basis frequency picks out one coordinate. -/
theorem freqDot_smul_single (ω : Fin k → ℝ) (t : ℝ) (j : Fin k) :
    freqDot ω (t • Pi.single j (1 : ℝ)) = t * ω j := by
  rw [freqDot, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]; ring
  · intro i _ hij
    rw [Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- If `t ↦ exp(i t a)` and `t ↦ exp(i t b)` agree for all real `t`, then `a = b`. -/
theorem exp_I_real_inj {a b : ℝ}
    (h : ∀ t : ℝ, Complex.exp (Complex.I * ((t * a : ℝ) : ℂ))
                = Complex.exp (Complex.I * ((t * b : ℝ) : ℂ))) : a = b := by
  by_contra hab
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hab
  have key := h (Real.pi / (a - b))
  have e1 : Complex.exp (Complex.I * ((Real.pi / (a - b) * a : ℝ) : ℂ))
          / Complex.exp (Complex.I * ((Real.pi / (a - b) * b : ℝ) : ℂ)) = 1 := by
    rw [key, div_self (Complex.exp_ne_zero _)]
  rw [← Complex.exp_sub] at e1
  have harg : Complex.I * ((Real.pi / (a - b) * a : ℝ) : ℂ)
            - Complex.I * ((Real.pi / (a - b) * b : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    rw [← mul_sub, ← Complex.ofReal_sub]
    have hpi : Real.pi / (a - b) * a - Real.pi / (a - b) * b = Real.pi := by
      rw [← mul_sub, div_mul_cancel₀ _ hc]
    rw [hpi]; ring
  rw [harg, Complex.exp_pi_mul_I] at e1
  norm_num at e1

/-- The character `x ↦ exp(i⟨ω,x⟩)` as a monoid homomorphism from the additive group of
data points (written multiplicatively) to `ℂ`. -/
noncomputable def chiHom (ω : Fin k → ℝ) : Multiplicative (Fin k → ℝ) →* ℂ where
  toFun := fun y => Complex.exp (Complex.I * (freqDot ω (Multiplicative.toAdd y) : ℂ))
  map_one' := by
    change Complex.exp (Complex.I *
      ((freqDot ω (Multiplicative.toAdd (1 : Multiplicative (Fin k → ℝ))) : ℝ) : ℂ)) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin k → ℝ))
        = (0 : Fin k → ℝ) from rfl]
    simp [freqDot]
  map_mul' := fun y₁ y₂ => by
    change Complex.exp (Complex.I * ((freqDot ω (Multiplicative.toAdd (y₁ * y₂)) : ℝ) : ℂ))
       = Complex.exp (Complex.I * ((freqDot ω (Multiplicative.toAdd y₁) : ℝ) : ℂ))
       * Complex.exp (Complex.I * ((freqDot ω (Multiplicative.toAdd y₂) : ℝ) : ℂ))
    rw [show Multiplicative.toAdd (y₁ * y₂)
          = Multiplicative.toAdd y₁ + Multiplicative.toAdd y₂ from rfl, freqDot_add_right]
    push_cast
    rw [mul_add, Complex.exp_add]

@[simp] theorem chiHom_apply (ω : Fin k → ℝ) (y : Multiplicative (Fin k → ℝ)) :
    (chiHom ω) y = Complex.exp (Complex.I * (freqDot ω (Multiplicative.toAdd y) : ℂ)) := rfl

/-- Distinct frequencies give distinct characters. -/
theorem chiHom_injective :
    Function.Injective
      (chiHom : (Fin k → ℝ) → (Multiplicative (Fin k → ℝ) →* ℂ)) := by
  intro ω ω' h
  funext j
  refine exp_I_real_inj (fun t => ?_)
  have hto : Multiplicative.toAdd (Multiplicative.ofAdd (t • Pi.single j (1 : ℝ)))
      = t • Pi.single j (1 : ℝ) := rfl
  have hc := DFunLike.congr_fun h (Multiplicative.ofAdd (t • Pi.single j (1 : ℝ)))
  simp only [chiHom_apply, hto, freqDot_smul_single] at hc
  exact hc

/-- **Uniqueness of trigonometric-polynomial coefficients.** A vanishing finite combination of the
distinct characters has all coefficients zero (Dedekind's independence of characters). -/
theorem expSum_coeff_zero_of_eval_zero {s : Finset (Fin k → ℝ)} {c : (Fin k → ℝ) → ℂ}
    (h : ∀ x, ∑ ω ∈ s, c ω * Complex.exp (Complex.I * (freqDot ω x : ℂ)) = 0) :
    ∀ ω ∈ s, c ω = 0 := by
  have hli : LinearIndependent ℂ (fun ω : Fin k → ℝ => ⇑(chiHom ω)) :=
    (linearIndependent_monoidHom (Multiplicative (Fin k → ℝ)) ℂ).comp chiHom chiHom_injective
  apply linearIndependent_iff'.mp hli s c
  funext y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chiHom_apply, Pi.zero_apply]
  exact h (Multiplicative.toAdd y)

/-- Two trigonometric polynomials with the same values have the same canonical coefficients. -/
theorem TrigPolynomial.coeffAt_eq_of_eval_eq {f g : TrigPolynomial k}
    (h : ∀ x, f.eval x = g.eval x) (ω : Fin k → ℝ) : f.coeffAt ω = g.coeffAt ω := by
  have hzero : ∀ x, ∑ ν ∈ f.freqs ∪ g.freqs,
      (f.coeffAt ν - g.coeffAt ν) * Complex.exp (Complex.I * (freqDot ν x : ℂ)) = 0 := by
    intro x
    have hf : f.eval x
        = ∑ ν ∈ f.freqs ∪ g.freqs,
            f.coeffAt ν * Complex.exp (Complex.I * (freqDot ν x : ℂ)) := by
      rw [TrigPolynomial.eval, ← Finset.sum_subset Finset.subset_union_left
            (fun ν _ hν => by rw [TrigPolynomial.coeffAt, if_neg hν, zero_mul])]
      exact Finset.sum_congr rfl (fun ν hν => by rw [TrigPolynomial.coeffAt, if_pos hν])
    have hg : g.eval x
        = ∑ ν ∈ f.freqs ∪ g.freqs,
            g.coeffAt ν * Complex.exp (Complex.I * (freqDot ν x : ℂ)) := by
      rw [TrigPolynomial.eval, ← Finset.sum_subset Finset.subset_union_right
            (fun ν _ hν => by rw [TrigPolynomial.coeffAt, if_neg hν, zero_mul])]
      exact Finset.sum_congr rfl (fun ν hν => by rw [TrigPolynomial.coeffAt, if_pos hν])
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, ← hf, ← hg, h x, sub_self]
  by_cases hω : ω ∈ f.freqs ∪ g.freqs
  · exact sub_eq_zero.mp
      (expSum_coeff_zero_of_eval_zero (c := fun ν => f.coeffAt ν - g.coeffAt ν) hzero ω hω)
  · rw [TrigPolynomial.coeffAt, TrigPolynomial.coeffAt,
        if_neg (fun hf => hω (Finset.mem_union_left _ hf)),
        if_neg (fun hg => hω (Finset.mem_union_right _ hg))]

/-- The canonical coefficient of a conjugated trigonometric polynomial negates the frequency and
conjugates. -/
theorem TrigPolynomial.coeffAt_conj (f : TrigPolynomial k) (ω : Fin k → ℝ) :
    (f.conj).coeffAt ω = (starRingEnd ℂ) (f.coeffAt (-ω)) := by
  have hmem : ω ∈ (f.conj).freqs ↔ -ω ∈ f.freqs := by
    simp only [TrigPolynomial.conj, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; rwa [neg_neg]
    · intro h; exact ⟨-ω, h, neg_neg ω⟩
  unfold TrigPolynomial.coeffAt
  by_cases h : -ω ∈ f.freqs
  · rw [if_pos (hmem.mpr h), if_pos h]; rfl
  · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h, map_zero]

/-! ### Frequency-set characterizations (for tracking which frequencies appear) -/

@[simp] theorem TrigPolynomial.smul_freqs (c : ℂ) (f : TrigPolynomial k) :
    (f.smul c).freqs = f.freqs := rfl

@[simp] theorem TrigPolynomial.expMul_freqs (a : Fin k → ℝ) (f : TrigPolynomial k) :
    (f.expMul a).freqs = f.freqs.image (fun ω => ω + a) := rfl

@[simp] theorem TrigPolynomial.conj_freqs (f : TrigPolynomial k) :
    (f.conj).freqs = f.freqs.image (fun ω => -ω) := rfl

@[simp] theorem TrigPolynomial.sum_freqs {ι : Type*} (s : Finset ι)
    (F : ι → TrigPolynomial k) :
    (TrigPolynomial.sum s F).freqs = s.biUnion (fun i => (F i).freqs) := rfl

theorem TrigPolynomial.mul_freqs (f g : TrigPolynomial k) :
    (f.mul g).freqs = f.freqs.biUnion (fun ω => g.freqs.image (fun ν => ν + ω)) := rfl

/-! ### Embedding into more variables (for products of sums in disjoint variable blocks) -/

section Embed
variable {m n : ℕ}

/-- The pairing of left-block-supported frequencies sees only the first block. -/
theorem freqDot_append_left (ω x : Fin m → ℝ) (y : Fin n → ℝ) :
    freqDot (Fin.append ω (0 : Fin n → ℝ)) (Fin.append x y) = freqDot ω x := by
  simp only [freqDot, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero]

/-- The pairing of right-block-supported frequencies sees only the second block. -/
theorem freqDot_append_right (ω : Fin n → ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    freqDot (Fin.append (0 : Fin m → ℝ) ω) (Fin.append x y) = freqDot ω y := by
  simp only [freqDot, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add]

/-- Embed an `m`-variable trigonometric polynomial into `m + n` variables on the first block. -/
noncomputable def TrigPolynomial.embedL (f : TrigPolynomial m) : TrigPolynomial (m + n) where
  freqs := f.freqs.image (fun ω => Fin.append ω (0 : Fin n → ℝ))
  coeff := fun σ => f.coeff (fun i => σ (Fin.castAdd n i))

/-- Embed an `n`-variable trigonometric polynomial into `m + n` variables on the second block. -/
noncomputable def TrigPolynomial.embedR (f : TrigPolynomial n) : TrigPolynomial (m + n) where
  freqs := f.freqs.image (fun ω => Fin.append (0 : Fin m → ℝ) ω)
  coeff := fun σ => f.coeff (fun i => σ (Fin.natAdd m i))

theorem TrigPolynomial.eval_embedL (f : TrigPolynomial m) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (f.embedL (n := n)).eval (Fin.append x y) = f.eval x := by
  simp only [TrigPolynomial.eval, TrigPolynomial.embedL]
  rw [Finset.sum_image (by
    intro p _ q _ hpq; funext i
    have := congrFun hpq (Fin.castAdd n i); simpa [Fin.append_left] using this)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [freqDot_append_left]
  congr 2
  funext i; rw [Fin.append_left]

theorem TrigPolynomial.eval_embedR (f : TrigPolynomial n) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (f.embedR (m := m)).eval (Fin.append x y) = f.eval y := by
  simp only [TrigPolynomial.eval, TrigPolynomial.embedR]
  rw [Finset.sum_image (by
    intro p _ q _ hpq; funext i
    have := congrFun hpq (Fin.natAdd m i); simpa [Fin.append_right] using this)]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [freqDot_append_right]
  congr 2
  funext i; rw [Fin.append_right]

@[simp] theorem TrigPolynomial.embedL_freqs (f : TrigPolynomial m) :
    (f.embedL (n := n)).freqs = f.freqs.image (fun ω => Fin.append ω (0 : Fin n → ℝ)) := rfl

@[simp] theorem TrigPolynomial.embedR_freqs (f : TrigPolynomial n) :
    (f.embedR (m := m)).freqs = f.freqs.image (fun ω => Fin.append (0 : Fin m → ℝ) ω) := rfl

end Embed

/-! ### One-variable parameter-shift identity -/

noncomputable section

/-- **Parameter-shift identity.** The derivative of `a + b cos θ + c sin θ`
equals the symmetric `π/2`-shifted finite difference `(C(θ+π/2) - C(θ-π/2))/2`. -/
theorem trig_parameter_shift (a b c θ : ℝ) :
    deriv (fun t => a + b * Real.cos t + c * Real.sin t) θ
      = ((a + b * Real.cos (θ + Real.pi / 2) + c * Real.sin (θ + Real.pi / 2))
          - (a + b * Real.cos (θ - Real.pi / 2) + c * Real.sin (θ - Real.pi / 2))) / 2 := by
  have hd : deriv (fun t => a + b * Real.cos t + c * Real.sin t) θ
      = -(b * Real.sin θ) + c * Real.cos θ := by
    have h1 : HasDerivAt (fun t : ℝ => b * Real.cos t) (-(b * Real.sin θ)) θ := by
      simpa using (Real.hasDerivAt_cos θ).const_mul b
    have h2 : HasDerivAt (fun t : ℝ => c * Real.sin t) (c * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).const_mul c
    have hH : HasDerivAt (fun t => a + b * Real.cos t + c * Real.sin t)
        (-(b * Real.sin θ) + c * Real.cos θ) θ := by
      simpa only [Pi.add_apply, add_assoc] using (h1.add h2).const_add a
    exact hH.deriv
  rw [hd, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

end

end QuantumAlg
