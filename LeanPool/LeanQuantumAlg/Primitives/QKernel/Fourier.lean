/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Util.TrigPolynomial
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Common
/-!
# Fourier representation of the quantum kernel

For an `N`-input data-encoding circuit with a common diagonal generator, the fidelity
quantum kernel `κ(x, x') = |⟨φ(x')|φ(x)⟩|²` is a finite sum of characters
`e^{i⟨s,x⟩} e^{i⟨t,x'⟩}` whose frequencies are differences of the generator's eigenvalues
(Schuld 2021). The encoding gates are modelled directly as diagonal phase matrices — the
standard WLOG-diagonalization step — so the Fourier structure is proved genuinely while
avoiding the matrix exponential.

The proof shows each component of the feature state is an `TrigPolynomial` (by closure under
applying a constant matrix and a diagonal phase gate), hence the overlap and its squared
modulus are `TrigPolynomial`s; collecting by frequency gives the representation.
-/

@[expose] public section

namespace QuantumAlg

open Complex BigOperators Matrix

variable {N d : ℕ}

/-- The diagonal data-encoding phase gate for input coordinate `k`:
`diagonal (μ ↦ exp(-i x_k λ_μ))`. -/
noncomputable def diagPhaseGate (lam : Fin d → ℝ) (xk : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun μ => Complex.exp (-Complex.I * ((xk * lam μ : ℝ) : ℂ)))

/-- A data-parametrized vector each of whose components is an trigonometric polynomial. -/
def IsTrigPolynomialVec (v : (Fin N → ℝ) → (Fin d → ℂ)) : Prop :=
  ∀ m, ∃ f : TrigPolynomial N, ∀ x, v x m = f.eval x

/-- Any constant vector is an trigonometric-polynomial vector (single zero frequency). -/
theorem isTrigPolynomialVec_const (w : Fin d → ℂ) :
    IsTrigPolynomialVec (fun _ : Fin N → ℝ => w) := by
  intro m
  refine ⟨⟨{0}, fun _ => w m⟩, fun x => ?_⟩
  simp [TrigPolynomial.eval, freqDot]

/-- Left-multiplication by a constant matrix preserves `IsTrigPolynomialVec`. -/
theorem IsTrigPolynomialVec.constMul {v : (Fin N → ℝ) → (Fin d → ℂ)}
    (hv : IsTrigPolynomialVec v) (M : Matrix (Fin d) (Fin d) ℂ) :
    IsTrigPolynomialVec (fun x => M *ᵥ v x) := by
  intro m
  choose f hf using hv
  refine ⟨TrigPolynomial.sum Finset.univ (fun j => (f j).smul (M m j)), fun x => ?_⟩
  change (M *ᵥ v x) m = _
  rw [TrigPolynomial.eval_sum, show (M *ᵥ v x) m = ∑ j, M m j * v x j from rfl]
  exact Finset.sum_congr rfl (fun j _ => by rw [TrigPolynomial.eval_smul, ← hf j x])

/-- Left-multiplication by a diagonal phase gate preserves `IsTrigPolynomialVec`. -/
theorem IsTrigPolynomialVec.phaseMul {v : (Fin N → ℝ) → (Fin d → ℂ)}
    (hv : IsTrigPolynomialVec v) (lam : Fin d → ℝ) (k : Fin N) :
    IsTrigPolynomialVec (fun x => diagPhaseGate lam (x k) *ᵥ v x) := by
  intro m
  obtain ⟨f, hf⟩ := hv m
  refine ⟨f.expMul (-(lam m) • Pi.single k (1 : ℝ)), fun x => ?_⟩
  change (diagPhaseGate lam (x k) *ᵥ v x) m = _
  simp only [diagPhaseGate, Matrix.mulVec_diagonal]
  rw [hf x, TrigPolynomial.eval_expMul]
  congr 1
  congr 1
  rw [freqDot_comm, freqDot_smul_single]
  push_cast
  ring

/-- The feature state after `j` encoding layers: start from `ψ`, apply the constant
unitary `W 0`, then alternately a phase gate for each coordinate and the next `W`.
`featState W lam ψ N x` is `|φ(x)⟩` for the full `N`-input circuit. -/
noncomputable def featState (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ)
    (lam : Fin d → ℝ) (ψ : Fin d → ℂ) :
    (j : ℕ) → (Fin N → ℝ) → (Fin d → ℂ)
  | 0, _ => W 0 *ᵥ ψ
  | (j + 1), x =>
      if h : j < N then
        W ⟨j + 1, by omega⟩
          *ᵥ (diagPhaseGate lam (x ⟨j, h⟩) *ᵥ featState W lam ψ j x)
      else featState W lam ψ j x

/-- Every layer of the feature state is an trigonometric-polynomial vector. -/
theorem isTrigPolynomialVec_featState (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ)
    (lam : Fin d → ℝ) (ψ : Fin d → ℂ) (j : ℕ) :
    IsTrigPolynomialVec (featState W lam ψ j) := by
  induction j with
  | zero => exact (isTrigPolynomialVec_const ψ).constMul (W 0)
  | succ j ih =>
      by_cases h : j < N
      · have heq : featState W lam ψ (j + 1)
            = fun x =>
              W ⟨j + 1, by omega⟩
                *ᵥ (diagPhaseGate lam (x ⟨j, h⟩) *ᵥ featState W lam ψ j x) := by
          funext x; simp only [featState, dif_pos h]
        rw [heq]
        exact (ih.phaseMul lam ⟨j, h⟩).constMul (W ⟨j + 1, by omega⟩)
      · have heq : featState W lam ψ (j + 1) = featState W lam ψ j := by
          funext x; simp only [featState, dif_neg h]
        rw [heq]; exact ih

/-! ### Constructive feature components (explicit trigonometric polynomials) -/

/-- A constant vector of trigonometric polynomials (each component a single zero-frequency term). -/
noncomputable def tpVecConst (w : Fin d → ℂ) : Fin d → TrigPolynomial N :=
  fun m => ⟨{0}, fun _ => w m⟩

theorem tpVecConst_eval (w : Fin d → ℂ) (m : Fin d) (x : Fin N → ℝ) :
    (tpVecConst w m).eval x = w m := by simp [tpVecConst, TrigPolynomial.eval, freqDot]

/-- Apply a constant matrix to a vector of trigonometric polynomials. -/
noncomputable def tpVecConstMul (M : Matrix (Fin d) (Fin d) ℂ) (V : Fin d → TrigPolynomial N) :
    Fin d → TrigPolynomial N :=
  fun m => TrigPolynomial.sum Finset.univ (fun j => (V j).smul (M m j))

theorem tpVecConstMul_eval (M : Matrix (Fin d) (Fin d) ℂ)
    (V : Fin d → TrigPolynomial N) (m : Fin d) (x : Fin N → ℝ) :
    (tpVecConstMul M V m).eval x = ∑ j, M m j * (V j).eval x := by
  simp only [tpVecConstMul, TrigPolynomial.eval_sum, TrigPolynomial.eval_smul]

/-- Apply a diagonal phase gate (symbolically, a per-component frequency shift). -/
noncomputable def tpVecPhase (lam : Fin d → ℝ) (k : Fin N) (V : Fin d → TrigPolynomial N) :
    Fin d → TrigPolynomial N :=
  fun m => (V m).expMul (-(lam m) • Pi.single k (1 : ℝ))

theorem tpVecPhase_eval (lam : Fin d → ℝ) (k : Fin N)
    (V : Fin d → TrigPolynomial N) (m : Fin d) (x : Fin N → ℝ) :
    (tpVecPhase lam k V m).eval x
      = Complex.exp (-Complex.I * ((x k * lam m : ℝ) : ℂ)) * (V m).eval x := by
  rw [tpVecPhase, TrigPolynomial.eval_expMul]
  congr 1
  rw [freqDot_comm, freqDot_smul_single]; push_cast; ring

/-- The constructive feature component after `j` layers: an explicit `Fin d`-indexed family
of trigonometric polynomials mirroring `featState`. -/
noncomputable def featCompC (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) : (j : ℕ) → Fin d → TrigPolynomial N
  | 0 => tpVecConstMul (W 0) (tpVecConst ψ)
  | (j + 1) =>
      if h : j < N then
        tpVecConstMul (W ⟨j + 1, by omega⟩) (tpVecPhase lam ⟨j, h⟩ (featCompC W lam ψ j))
      else featCompC W lam ψ j

theorem featState_eq_featCompC (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ)
    (lam : Fin d → ℝ) (ψ : Fin d → ℂ) (j : ℕ) :
    ∀ (x : Fin N → ℝ) (m : Fin d),
      featState W lam ψ j x m = (featCompC W lam ψ j m).eval x := by
  induction j with
  | zero =>
      intro x m
      change (W 0 *ᵥ ψ) m = _
      rw [featCompC, tpVecConstMul_eval]
      simp only [tpVecConst_eval]
      rfl
  | succ j ih =>
      intro x m
      by_cases h : j < N
      · have hs : featState W lam ψ (j + 1) x m
            = (W ⟨j + 1, by omega⟩
              *ᵥ (diagPhaseGate lam (x ⟨j, h⟩) *ᵥ featState W lam ψ j x)) m := by
          simp only [featState, dif_pos h]
        have hc : featCompC W lam ψ (j + 1) m
            = tpVecConstMul (W ⟨j + 1, by omega⟩)
              (tpVecPhase lam ⟨j, h⟩ (featCompC W lam ψ j)) m := by
          simp only [featCompC, dif_pos h]
        rw [hs, hc, tpVecConstMul_eval,
          show (W ⟨j + 1, by omega⟩
              *ᵥ (diagPhaseGate lam (x ⟨j, h⟩) *ᵥ featState W lam ψ j x)) m
              = ∑ i, W ⟨j + 1, by omega⟩ m i
                  * (diagPhaseGate lam (x ⟨j, h⟩) *ᵥ featState W lam ψ j x) i from rfl]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [tpVecPhase_eval]
        congr 1
        rw [diagPhaseGate, Matrix.mulVec_diagonal, ih x i]
      · have hs : featState W lam ψ (j + 1) x m = featState W lam ψ j x m := by
          simp only [featState, dif_neg h]
        have hc : featCompC W lam ψ (j + 1) m = featCompC W lam ψ j m := by
          simp only [featCompC, dif_neg h]
        rw [hs, hc]; exact ih x m

/-- The trigonometric-polynomial witness for component `m` of the full feature state. -/
noncomputable def featComp (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (m : Fin d) : TrigPolynomial N :=
  featCompC W lam ψ N m

theorem featComp_eval (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (m : Fin d) (x : Fin N → ℝ) :
    featState W lam ψ N x m = (featComp W lam ψ m).eval x :=
  featState_eq_featCompC W lam ψ N x m

/-! ### Feature-component frequency invariant -/

theorem tpVecConst_freqs (w : Fin d → ℂ) (m : Fin d) :
    (tpVecConst w m).freqs = ({0} : Finset (Fin N → ℝ)) := rfl

theorem tpVecConstMul_freqs (M : Matrix (Fin d) (Fin d) ℂ)
    (V : Fin d → TrigPolynomial N) (m : Fin d) :
    (tpVecConstMul M V m).freqs = Finset.univ.biUnion (fun j => (V j).freqs) := by
  simp only [tpVecConstMul, TrigPolynomial.sum_freqs, TrigPolynomial.smul_freqs]

theorem tpVecPhase_freqs (lam : Fin d → ℝ) (k : Fin N)
    (V : Fin d → TrigPolynomial N) (m : Fin d) :
    (tpVecPhase lam k V m).freqs
      = (V m).freqs.image (fun ω => ω + -(lam m) • Pi.single k (1 : ℝ)) := by
  simp only [tpVecPhase, TrigPolynomial.expMul_freqs]

/-- After `j` layers, every feature-component frequency is `-λ_μ` on coordinates `< j` and
`0` on coordinates `≥ j`. Since each input is encoded exactly once, at `j = N` every
coordinate is a negated eigenvalue. -/
theorem featCompC_layer (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) :
    ∀ (j : ℕ) (m : Fin d) (ω : Fin N → ℝ), ω ∈ (featCompC W lam ψ j m).freqs →
      ∀ a : Fin N,
        ((a : ℕ) < j → ∃ μ, ω a = -lam μ) ∧ (j ≤ (a : ℕ) → ω a = 0) := by
  intro j
  induction j with
  | zero =>
      intro m ω hω a
      rw [show featCompC W lam ψ 0 = tpVecConstMul (W 0) (tpVecConst ψ) from rfl,
        tpVecConstMul_freqs] at hω
      simp only [tpVecConst_freqs, Finset.mem_biUnion, Finset.mem_singleton] at hω
      obtain ⟨i, -, rfl⟩ := hω
      exact ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ j ih =>
      intro m ω hω a
      by_cases hj : j < N
      · have hfc : featCompC W lam ψ (j + 1) m
            = tpVecConstMul (W ⟨j + 1, by omega⟩)
              (tpVecPhase lam ⟨j, hj⟩ (featCompC W lam ψ j)) m := by
          simp only [featCompC, dif_pos hj]
        rw [hfc, tpVecConstMul_freqs] at hω
        simp only [tpVecPhase_freqs, Finset.mem_biUnion, Finset.mem_image] at hω
        obtain ⟨i, -, ω', hω', rfl⟩ := hω
        obtain ⟨hlt, hge⟩ := ih i ω' hω' a
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
          mul_one, mul_zero]
        refine ⟨fun hlt1 => ?_, fun hge2 => ?_⟩
        · by_cases hak : a = (⟨j, hj⟩ : Fin N)
          · have haj : (a : ℕ) = j := by rw [hak]
            rw [if_pos hak, hge (by omega)]
            exact ⟨i, by ring⟩
          · rw [if_neg hak, add_zero]
            refine hlt ?_
            have hne : (a : ℕ) ≠ j := fun he => hak (Fin.ext he)
            omega
        · have hak : a ≠ (⟨j, hj⟩ : Fin N) := by
            intro he
            have hcontra : (a : ℕ) = j := by
              rw [he]
            omega
          rw [if_neg hak, add_zero]
          exact hge (by omega)
      · have hfc : featCompC W lam ψ (j + 1) m = featCompC W lam ψ j m := by
          simp only [featCompC, dif_neg hj]
        rw [hfc] at hω
        obtain ⟨hlt, hge⟩ := ih m ω hω a
        have hN : N ≤ j := Nat.not_lt.mp hj
        refine ⟨fun _ => hlt (Nat.lt_of_lt_of_le a.isLt hN), fun hge2 => ?_⟩
        exfalso
        have ha := a.isLt
        omega

/-- At the full circuit (`j = N`), every feature-component frequency coordinate is a
negated eigenvalue. -/
theorem featComp_freq (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (m : Fin d) (ω : Fin N → ℝ) (hω : ω ∈ (featComp W lam ψ m).freqs)
    (a : Fin N) : ∃ μ, ω a = -lam μ :=
  (featCompC_layer W lam ψ N m ω hω a).1 a.isLt

/-- The overlap `⟨φ(x')|φ(x)⟩` as a trigonometric polynomial in the concatenated
variable. -/
noncomputable def overlapES (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) : TrigPolynomial (N + N) :=
  TrigPolynomial.sum Finset.univ
    (fun m =>
      ((featComp W lam ψ m).conj.embedR (m := N)).mul
        ((featComp W lam ψ m).embedL (n := N)))

theorem overlapES_eval (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (x x' : Fin N → ℝ) :
    (overlapES W lam ψ).eval (Fin.append x x')
      = ∑ m, (starRingEnd ℂ) (featState W lam ψ N x' m) * featState W lam ψ N x m := by
  rw [overlapES, TrigPolynomial.eval_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [TrigPolynomial.eval_mul, TrigPolynomial.eval_embedL, TrigPolynomial.eval_embedR,
      TrigPolynomial.eval_conj,
      ← featComp_eval W lam ψ m x', ← featComp_eval W lam ψ m x]

/-- The quantum kernel as an trigonometric polynomial: the squared modulus of the overlap. -/
noncomputable def kernelES (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) : TrigPolynomial (N + N) :=
  (overlapES W lam ψ).mul (overlapES W lam ψ).conj

/-- **Fourier representation of the quantum kernel** (Schuld 2021). The fidelity kernel
`κ(x,x') = |⟨φ(x')|φ(x)⟩|²` is a finite sum of characters `e^{i⟨ω,(x,x')⟩}` whose
frequencies (the elements of `(kernelES …).freqs`) are differences of the generator's
eigenvalue vectors. -/
theorem fourier_representation (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ)
    (lam : Fin d → ℝ) (ψ : Fin d → ℂ) (x x' : Fin N → ℝ) :
    (Complex.normSq
      (∑ m, (starRingEnd ℂ) (featState W lam ψ N x' m) * featState W lam ψ N x m) : ℂ)
      = ∑ ω ∈ (kernelES W lam ψ).freqs,
          (kernelES W lam ψ).coeff ω
            * Complex.exp (Complex.I * (freqDot ω (Fin.append x x') : ℂ)) := by
  have hov := overlapES_eval W lam ψ x x'
  change _ = (kernelES W lam ψ).eval (Fin.append x x')
  rw [kernelES, TrigPolynomial.eval_mul, TrigPolynomial.eval_conj, ← hov, Complex.mul_conj]

/-- **Reality condition.** The kernel's Fourier coefficients are conjugate-symmetric under
frequency negation, which is exactly what makes the kernel real-valued. -/
theorem fourier_real (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (ω : Fin (N + N) → ℝ) :
    (kernelES W lam ψ).coeffAt ω = (starRingEnd ℂ) ((kernelES W lam ψ).coeffAt (-ω)) := by
  have hk : ∀ z, (kernelES W lam ψ).eval z
      = (↑(Complex.normSq ((overlapES W lam ψ).eval z)) : ℂ) := by
    intro z; rw [kernelES, TrigPolynomial.eval_mul, TrigPolynomial.eval_conj, Complex.mul_conj]
  rw [← TrigPolynomial.coeffAt_conj]
  refine TrigPolynomial.coeffAt_eq_of_eval_eq (fun z => ?_) ω
  rw [TrigPolynomial.eval_conj]
  simp only [hk]
  rw [Complex.conj_ofReal]

/-! ### Integer-spectrum corollary -/

/-- Every overlap frequency is a negated eigenvalue on the first block and an eigenvalue on
the second block. -/
theorem overlapES_freq (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (σ : Fin (N + N) → ℝ) (hσ : σ ∈ (overlapES W lam ψ).freqs) :
    (∀ a : Fin N, ∃ μ, σ (Fin.castAdd N a) = -lam μ) ∧
    (∀ a : Fin N, ∃ ν, σ (Fin.natAdd N a) = lam ν) := by
  rw [overlapES, TrigPolynomial.sum_freqs, Finset.mem_biUnion] at hσ
  obtain ⟨m, -, hσm⟩ := hσ
  rw [TrigPolynomial.mul_freqs, Finset.mem_biUnion] at hσm
  obtain ⟨ω, hω, hσω⟩ := hσm
  rw [Finset.mem_image] at hσω
  obtain ⟨ν, hν, rfl⟩ := hσω
  rw [TrigPolynomial.embedR_freqs, Finset.mem_image] at hω
  obtain ⟨x, hx, rfl⟩ := hω
  rw [TrigPolynomial.conj_freqs, Finset.mem_image] at hx
  obtain ⟨ω₁, hω₁, rfl⟩ := hx
  rw [TrigPolynomial.embedL_freqs, Finset.mem_image] at hν
  obtain ⟨ν₁, hν₁, rfl⟩ := hν
  refine ⟨fun a => ?_, fun a => ?_⟩
  · obtain ⟨μ, hμ⟩ := featComp_freq W lam ψ m ν₁ hν₁ a
    refine ⟨μ, ?_⟩
    rw [Pi.add_apply, Fin.append_left, Fin.append_left, Pi.zero_apply, add_zero, hμ]
  · obtain ⟨ν', hν'⟩ := featComp_freq W lam ψ m ω₁ hω₁ a
    refine ⟨ν', ?_⟩
    rw [Pi.add_apply, Fin.append_right, Fin.append_right, Pi.zero_apply, zero_add,
      Pi.neg_apply, hν', neg_neg]

/-- **Integer-spectrum corollary** (Schuld 2021). If every eigenvalue difference is an
integer, every kernel frequency has integer coordinates — the kernel is a genuine
multidimensional Fourier series. -/
theorem fourier_integer_spectrum
    (W : Fin (N + 1) → Matrix (Fin d) (Fin d) ℂ) (lam : Fin d → ℝ)
    (ψ : Fin d → ℂ) (hint : ∀ i j : Fin d, ∃ z : ℤ, lam i - lam j = z)
    (σ : Fin (N + N) → ℝ) (hσ : σ ∈ (kernelES W lam ψ).freqs) (a : Fin (N + N)) :
    ∃ z : ℤ, σ a = z := by
  rw [kernelES, TrigPolynomial.mul_freqs, Finset.mem_biUnion] at hσ
  obtain ⟨ω, hω, hσω⟩ := hσ
  rw [Finset.mem_image] at hσω
  obtain ⟨ν, hν, rfl⟩ := hσω
  rw [TrigPolynomial.conj_freqs, Finset.mem_image] at hν
  obtain ⟨ν', hν', rfl⟩ := hν
  obtain ⟨hωc, hωn⟩ := overlapES_freq W lam ψ ω hω
  obtain ⟨hν'c, hν'n⟩ := overlapES_freq W lam ψ ν' hν'
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a
  · obtain ⟨μ, hμ⟩ := hωc a
    obtain ⟨μ', hμ'⟩ := hν'c a
    obtain ⟨z, hz⟩ := hint μ' μ
    refine ⟨z, ?_⟩
    simp only [Pi.add_apply, Pi.neg_apply, hμ, hμ']
    rw [← hz]; ring
  · obtain ⟨ν₂, hν₂⟩ := hωn a
    obtain ⟨ν₃, hν₃⟩ := hν'n a
    obtain ⟨z, hz⟩ := hint ν₂ ν₃
    refine ⟨z, ?_⟩
    simp only [Pi.add_apply, Pi.neg_apply, hν₂, hν₃]
    rw [← hz]; ring

/-! ### Non-vacuity witness: the Pauli-X encoding reproduces the cos² kernel -/

/-- Eigenvalues of `½σ_x`: `(-1/2, 1/2)`. -/
noncomputable def pauliXSpectrum : Fin 2 → ℝ := ![-(1 / 2), 1 / 2]

/-- Uniform initial state `(1/√2, 1/√2)`. -/
noncomputable def pauliXPsi : Fin 2 → ℂ :=
  ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]

/-- Trivial surrounding unitaries (identity): the data is encoded by the diagonal gate alone. -/
noncomputable def pauliXW : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![1, 1]

/-- The single-qubit cosine-encoding feature state is `(e^{ix/2}/√2, e^{-ix/2}/√2)`. -/
theorem pauliX_featState (x : ℝ) :
    featState pauliXW pauliXSpectrum pauliXPsi 1 ![x]
      = ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * ↑(x / 2)),
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ↑(x / 2)))] := by
  have hstep : featState pauliXW pauliXSpectrum pauliXPsi 1 ![x]
      = (1 : Matrix (Fin 2) (Fin 2) ℂ)
          *ᵥ (diagPhaseGate pauliXSpectrum x
            *ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ pauliXPsi)) := rfl
  rw [hstep, Matrix.one_mulVec, Matrix.one_mulVec]
  funext i
  fin_cases i
  · simp only [diagPhaseGate, pauliXSpectrum, pauliXPsi, Matrix.mulVec_diagonal]
    rw [mul_comm]; congr 1; congr 1; push_cast; ring
  · simp only [diagPhaseGate, pauliXSpectrum, pauliXPsi, Matrix.mulVec_diagonal]
    rw [mul_comm]; congr 1; congr 1; push_cast; ring

/-- **Non-vacuity witness** (Schuld 2021). The single-qubit cosine-encoding quantum kernel
equals the squared-cosine kernel `cos²((x-x')/2)`. -/
theorem pauliX_kernel_eq_cos_sq (x x' : ℝ) :
    Complex.normSq
        (∑ m, (starRingEnd ℂ) (featState pauliXW pauliXSpectrum pauliXPsi 1 ![x'] m)
          * featState pauliXW pauliXSpectrum pauliXPsi 1 ![x] m)
      = Real.cos ((x - x') / 2) ^ 2 := by
  have hr2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hcosG : (1 / 2 : ℂ) * (Complex.exp (Complex.I * ↑((x - x') / 2))
        + Complex.exp (-(Complex.I * ↑((x - x') / 2))))
      = (↑(Real.cos ((x - x') / 2)) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos, mul_comm (↑((x - x') / 2) : ℂ) Complex.I,
      show -(↑((x - x') / 2) : ℂ) * Complex.I = -(Complex.I * ↑((x - x') / 2)) from by ring]
    ring
  have hconj1 : (starRingEnd ℂ) (Complex.exp (Complex.I * ↑(x' / 2)))
      = Complex.exp (-(Complex.I * ↑(x' / 2))) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj2 : (starRingEnd ℂ) (Complex.exp (-(Complex.I * ↑(x' / 2))))
      = Complex.exp (Complex.I * ↑(x' / 2)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [pauliX_featState, pauliX_featState, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, Complex.conj_ofReal, hconj1,
    hconj2]
  rw [show (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ↑(x' / 2)))
          * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * ↑(x / 2)))
        + (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * ↑(x' / 2))
          * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.exp (-(Complex.I * ↑(x / 2))))
        = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * (Complex.exp (-(Complex.I * ↑(x' / 2)) + Complex.I * ↑(x / 2))
            + Complex.exp (Complex.I * ↑(x' / 2) + -(Complex.I * ↑(x / 2)))) from by
      rw [Complex.exp_add, Complex.exp_add]; ring]
  rw [show -(Complex.I * ↑(x' / 2)) + Complex.I * ↑(x / 2) = Complex.I * ↑((x - x') / 2)
        from by push_cast; ring,
    show Complex.I * ↑(x' / 2) + -(Complex.I * ↑(x / 2)) = -(Complex.I * ↑((x - x') / 2))
        from by push_cast; ring,
    hr2, hcosG, Complex.normSq_ofReal]
  ring

end QuantumAlg
