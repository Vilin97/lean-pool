/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Bounds for actual Fréchet jets

Finite jet bounds on open domains, using `iteratedFDeriv` itself.  The product
estimates follow from Mathlib's higher-order Leibniz inequality.  No PDE,
construction, or prescribed derivative values are assumed here.
-/

@[expose] public section


namespace NavierStokes.JetBounds

noncomputable section

open scoped BigOperators ContDiff

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A common bound for the actual derivatives of orders `0, ..., m` on `s`.
Smoothness is a separate hypothesis of the closure theorems. -/
def FiniteJetBound (m : ℕ) (f : D → E) (s : Set D) (C : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ m → ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C

/-- An order-dependent bound for all actual derivatives on `s`. -/
def AllJetBound (f : D → E) (s : Set D) (C : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∀ x ∈ s, ‖iteratedFDeriv ℝ n f x‖ ≤ C n

theorem FiniteJetBound.mono {m : ℕ} {f : D → E} {s : Set D} {A B : ℝ}
    (hf : FiniteJetBound m f s A) (hAB : A ≤ B) : FiniteJetBound m f s B :=
  fun n hn x hx => (hf n hn x hx).trans hAB

theorem FiniteJetBound.of_le {m n : ℕ} {f : D → E} {s : Set D} {C : ℝ}
    (hf : FiniteJetBound m f s C) (hn : n ≤ m) : FiniteJetBound n f s C :=
  fun i hi x hx => hf i (hi.trans hn) x hx

theorem FiniteJetBound.nonneg {m : ℕ} {f : D → E} {s : Set D} {C : ℝ}
    (hf : FiniteJetBound m f s C) {x : D} (hx : x ∈ s) : 0 ≤ C :=
  (norm_nonneg _).trans (hf 0 (Nat.zero_le _) x hx)

theorem FiniteJetBound.norm_le {m : ℕ} {f : D → E} {s : Set D} {C : ℝ}
    (hf : FiniteJetBound m f s C) {x : D} (hx : x ∈ s) : ‖f x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using hf 0 (Nat.zero_le _) x hx

/-- Taking a genuine Fréchet derivative consumes one derivative of the bound. -/
theorem FiniteJetBound.fderiv {m : ℕ} {f : D → E} {s : Set D} {C : ℝ}
    (hf : FiniteJetBound (m + 1) f s C) :
    FiniteJetBound m (fderiv ℝ f) s C := by
  intro n hn x hx
  rw [norm_iteratedFDeriv_fderiv]
  exact hf (n + 1) (Nat.add_le_add_right hn 1) x hx

theorem AllJetBound.fderiv {f : D → E} {s : Set D} {C : ℕ → ℝ}
    (hf : AllJetBound f s C) :
    AllJetBound (fderiv ℝ f) s (fun n => C (n + 1)) := by
  intro n x hx
  rw [norm_iteratedFDeriv_fderiv]
  exact hf (n + 1) x hx

/-- Addition in a finite `C^m` bound, on an arbitrary open domain. -/
theorem FiniteJetBound.add {m : ℕ} {f g : D → E} {s : Set D} {A B : ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ m g s)
    (hA : FiniteJetBound m f s A) (hB : FiniteJetBound m g s B) :
    FiniteJetBound m (fun x => f x + g x) s (A + B) := by
  intro n hn x hx
  have hfn : ContDiffAt ℝ n f x :=
    (hf.contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast hn)
  have hgn : ContDiffAt ℝ n g x :=
    (hg.contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast hn)
  rw [fun_iteratedFDeriv_add_apply hfn hgn]
  exact (norm_add_le _ _).trans (add_le_add (hA n hn x hx) (hB n hn x hx))

/-- Mathlib's Leibniz inequality stated with ambient derivatives on an open set. -/
theorem norm_iteratedFDeriv_bilinear_le_on (B : E →L[ℝ] F →L[ℝ] G)
    {f : D → E} {g : D → F} {s : Set D} {N : WithTop ℕ∞}
    (hs : IsOpen s) (hf : ContDiffOn ℝ N f s) (hg : ContDiffOn ℝ N g s)
    {x : D} (hx : x ∈ s) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hs.uniqueDiffOn hx hn
  have hf' (i : ℕ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hs hx
  have hg' (i : ℕ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) i hs hx
  rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
  simpa only [hf', hg'] using h

/-- The scalar Leibniz inequality on an open set, with ambient derivatives. -/
theorem norm_iteratedFDeriv_mul_le_on {f g : D → ℝ} {s : Set D}
    {N : WithTop ℕ∞} (hs : IsOpen s) (hf : ContDiffOn ℝ N f s)
    (hg : ContDiffOn ℝ N g s) {x : D} (hx : x ∈ s) {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  have h := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn hx hn
  have hf' (i : ℕ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hs hx
  have hg' (i : ℕ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) i hs hx
  rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
  simpa only [hf', hg'] using h

private theorem sum_choose_real (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.sum_range_choose n

private theorem binomial_norm_sum_le {m n : ℕ} {f : D → E} {g : D → F}
    {s : Set D} {A B : ℝ} (hA : FiniteJetBound m f s A)
    (hB : FiniteJetBound m g s B) (hn : n ≤ m) {x : D} (hx : x ∈ s) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
      (2 : ℝ) ^ m * A * B := by
  have hA0 : 0 ≤ A := hA.nonneg hx
  have hB0 : 0 ≤ B := hB.nonneg hx
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hA i (hin.trans hn) x hx) (Nat.cast_nonneg _)
      · exact hB (n - i) ((Nat.sub_le _ _).trans hn) x hx
      · exact norm_nonneg _
      · exact mul_nonneg (Nat.cast_nonneg _) hA0
    _ = (2 : ℝ) ^ n * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_choose_real]
    _ ≤ (2 : ℝ) ^ m * A * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hA0) hB0

/-- A bounded bilinear map obeys the explicit finite-order Leibniz bound. -/
theorem FiniteJetBound.bilinear {m : ℕ} (B : E →L[ℝ] F →L[ℝ] G)
    {f : D → E} {g : D → F} {s : Set D} {A C : ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ m g s)
    (hA : FiniteJetBound m f s A) (hC : FiniteJetBound m g s C) :
    FiniteJetBound m (fun x => B (f x) (g x)) s (‖B‖ * (2 : ℝ) ^ m * A * C) := by
  intro n hn x hx
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
      norm_iteratedFDeriv_bilinear_le_on B hs hf hg hx (by exact_mod_cast hn)
    _ ≤ ‖B‖ * ((2 : ℝ) ^ m * A * C) :=
      mul_le_mul_of_nonneg_left (binomial_norm_sum_le hA hC hn hx) (norm_nonneg B)
    _ = _ := by ring

/-- Scalar multiplication has bilinear norm at most one, giving constant `2^m`. -/
theorem FiniteJetBound.mul {m : ℕ} {f g : D → ℝ} {s : Set D} {A B : ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ m g s)
    (hA : FiniteJetBound m f s A) (hB : FiniteJetBound m g s B) :
    FiniteJetBound m (fun x => f x * g x) s ((2 : ℝ) ^ m * A * B) := by
  intro n hn x hx
  exact (norm_iteratedFDeriv_mul_le_on hs hf hg hx (by exact_mod_cast hn)).trans
    (binomial_norm_sum_le hA hB hn hx)

/-- Evaluation of an operator-valued field has the same `2^m` product bound. -/
theorem FiniteJetBound.clm_apply {m : ℕ} {f : D → E →L[ℝ] F} {g : D → E}
    {s : Set D} {A B : ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ m g s)
    (hA : FiniteJetBound m f s A) (hB : FiniteJetBound m g s B) :
    FiniteJetBound m (fun x => (f x) (g x)) s ((2 : ℝ) ^ m * A * B) := by
  intro n hn x hx
  have h := norm_iteratedFDerivWithin_clm_apply hf hg hs.uniqueDiffOn hx
    (n := n) (by exact_mod_cast hn)
  have hf' (i : ℕ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) i hs hx
  have hg' (i : ℕ) := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g) i hs hx
  rw [iteratedFDerivWithin_of_isOpen _ hs hx] at h
  simp only [hf', hg'] at h
  exact h.trans (binomial_norm_sum_le hA hB hn hx)

/-- The transport expression `(Dg) f` uses one extra derivative of `g`. -/
theorem FiniteJetBound.transport {m : ℕ} {f : D → D} {g : D → E}
    {s : Set D} {A B : ℝ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ (m + 1) g s)
    (hA : FiniteJetBound m f s A) (hB : FiniteJetBound (m + 1) g s B) :
    FiniteJetBound m (fun x => _root_.fderiv ℝ g x (f x)) s ((2 : ℝ) ^ m * B * A) := by
  have hg' : ContDiffOn ℝ m (_root_.fderiv ℝ g) s :=
    hg.fderiv_of_isOpen hs (by simp)
  exact FiniteJetBound.clm_apply hs hg' hf hB.fderiv hA

/-- The actual second Fréchet derivative consumes two orders of a finite bound. -/
theorem FiniteJetBound.secondFDeriv {m : ℕ} {f : D → E} {s : Set D} {C : ℝ}
    (hf : FiniteJetBound (m + 2) f s C) :
    FiniteJetBound m (_root_.fderiv ℝ (_root_.fderiv ℝ f)) s C :=
  hf.fderiv.fderiv

/-- The order profile produced by the binomial Leibniz sum. -/
def leibnizProfile (A B : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i)

private theorem binomial_norm_sum_le_profile {f : D → E} {g : D → F}
    {s : Set D} {A B : ℕ → ℝ} (hA : AllJetBound f s A)
    (hB : AllJetBound g s B) (n : ℕ) {x : D} (hx : x ∈ s) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) ≤
      leibnizProfile A B n := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (hA i x hx) (Nat.cast_nonneg _)
  · exact hB (n - i) x hx
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hA i x hx))

theorem AllJetBound.add {f g : D → E} {s : Set D} {A B : ℕ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    (hA : AllJetBound f s A) (hB : AllJetBound g s B) :
    AllJetBound (fun x => f x + g x) s (fun n => A n + B n) := by
  intro n x hx
  have hfn : ContDiffAt ℝ n f x := (hf.contDiffAt (hs.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hgn : ContDiffAt ℝ n g x := (hg.contDiffAt (hs.mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  rw [fun_iteratedFDeriv_add_apply hfn hgn]
  exact (norm_add_le _ _).trans (add_le_add (hA n x hx) (hB n x hx))

/-- All-order bilinear closure with the full binomial profile, rather than a
constant uniform in derivative order. -/
theorem AllJetBound.bilinear (L : E →L[ℝ] F →L[ℝ] G)
    {f : D → E} {g : D → F} {s : Set D} {A B : ℕ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    (hA : AllJetBound f s A) (hB : AllJetBound g s B) :
    AllJetBound (fun x => L (f x) (g x)) s (fun n => ‖L‖ * leibnizProfile A B n) := by
  intro n x hx
  exact (norm_iteratedFDeriv_bilinear_le_on L hs hf hg hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).trans
    (mul_le_mul_of_nonneg_left (binomial_norm_sum_le_profile hA hB n hx) (norm_nonneg L))

theorem AllJetBound.mul {f g : D → ℝ} {s : Set D} {A B : ℕ → ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    (hA : AllJetBound f s A) (hB : AllJetBound g s B) :
    AllJetBound (fun x => f x * g x) s (leibnizProfile A B) := by
  intro n x hx
  exact (norm_iteratedFDeriv_mul_le_on hs hf hg hx
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).trans
    (binomial_norm_sum_le_profile hA hB n hx)

theorem leibnizProfile_scale (A B : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    leibnizProfile (fun i => A i * a) (fun i => B i * b) n =
      leibnizProfile A B n * (a * b) := by
  unfold leibnizProfile
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact exponent addition in the finite product bound. -/
theorem FiniteJetBound.mul_rpow {m : ℕ} {f g : D → ℝ} {s : Set D}
    {A B ε α β : ℝ} (hε : 0 < ε) (hs : IsOpen s)
    (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ m g s)
    (hA : FiniteJetBound m f s (A * ε ^ α))
    (hB : FiniteJetBound m g s (B * ε ^ β)) :
    FiniteJetBound m (fun x => f x * g x) s
      ((2 : ℝ) ^ m * A * B * ε ^ (α + β)) := by
  apply (FiniteJetBound.mul hs hf hg hA hB).mono
  apply le_of_eq
  rw [Real.rpow_add hε]
  ring

/-- The all-order product estimate preserves the sum of real decay exponents;
the output constants are explicitly the binomial convolution of input constants. -/
theorem AllJetBound.mul_rpow {f g : D → ℝ} {s : Set D}
    {A B : ℕ → ℝ} {ε α β : ℝ} (hε : 0 < ε) (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    (hA : AllJetBound f s (fun n => A n * ε ^ α))
    (hB : AllJetBound g s (fun n => B n * ε ^ β)) :
    AllJetBound (fun x => f x * g x) s
      (fun n => leibnizProfile A B n * ε ^ (α + β)) := by
  have h := AllJetBound.mul hs hf hg hA hB
  intro n x hx
  simpa only [leibnizProfile_scale, Real.rpow_add hε] using h n x hx

/-- Quantitative change of a general bounded bilinear nonlinearity.  The three
terms are the two cross interactions and the quadratic perturbation. -/
theorem FiniteJetBound.bilinear_perturbation {m : ℕ} (L : E →L[ℝ] F →L[ℝ] G)
    {f u : D → E} {g v : D → F} {s : Set D} {A U B V : ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ m f s) (hu : ContDiffOn ℝ m u s)
    (hg : ContDiffOn ℝ m g s) (hv : ContDiffOn ℝ m v s)
    (hA : FiniteJetBound m f s A) (hU : FiniteJetBound m u s U)
    (hB : FiniteJetBound m g s B) (hV : FiniteJetBound m v s V) :
    FiniteJetBound m
      (fun x => L (f x + u x) (g x + v x) - L (f x) (g x)) s
      (‖L‖ * (2 : ℝ) ^ m * (A * V + U * B + U * V)) := by
  have hfv : ContDiffOn ℝ m (fun x => L (f x) (v x)) s :=
    (L.contDiff.comp_contDiffOn hf).clm_apply hv
  have hug : ContDiffOn ℝ m (fun x => L (u x) (g x)) s :=
    (L.contDiff.comp_contDiffOn hu).clm_apply hg
  have huv : ContDiffOn ℝ m (fun x => L (u x) (v x)) s :=
    (L.contDiff.comp_contDiffOn hu).clm_apply hv
  have h₁ := FiniteJetBound.bilinear L hs hf hv hA hV
  have h₂ := FiniteJetBound.bilinear L hs hu hg hU hB
  have h₃ := FiniteJetBound.bilinear L hs hu hv hU hV
  have hsum := FiniteJetBound.add hs (hfv.add hug) huv
    (FiniteJetBound.add hs hfv hug h₁ h₂) h₃
  have heq : (fun x => L (f x + u x) (g x + v x) - L (f x) (g x)) =
      (fun x => (L (f x) (v x) + L (u x) (g x)) + L (u x) (v x)) := by
    funext x
    simp only [map_add, add_apply]
    abel
  rw [heq]
  apply hsum.mono
  exact le_of_eq (by ring)

end

end NavierStokes.JetBounds
