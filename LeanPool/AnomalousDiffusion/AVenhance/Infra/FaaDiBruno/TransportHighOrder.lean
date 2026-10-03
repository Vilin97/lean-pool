/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportCharacteristicJets
public import Mathlib.Analysis.Normed.Lp.PiLp

/-! # Transport High Order

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- The finite array of all coordinate partials of order `n` at one point. -/
def orderedSpatialJetArray (n : ℕ) (f : Vec 2 → Vec 2) (x : Vec 2) :
    (Fin n → Fin 2) → Vec 2 :=
  fun I => orderedPartial n f x I

/-- The array of recursively differentiated transport sources for all
coordinate partials of order `n`. -/
def transportSpatialSourceArray (n : ℕ) (b g Y : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (x : Vec 2) : (Fin n → Fin 2) → Vec 2 :=
  fun I => transportSourceJet
    (List.ofFn fun j => coordinateVector 2 (I j)) b g Y (t, x)

/-- The lower-allocation weight after inserting the induction bound
`16 C_g s` in the transport source estimate. -/
def transportLowerAllocationWeight (n m : ℕ) (C_f C_g R ρ s : ℝ) : ℝ :=
  if 2 ≤ m then
    C_f * m.factorial * R ^ m / (m + 1 : ℝ) ^ 2 *
      (16 * C_g * s * (n - m + 1).factorial * ρ ^ (n - m + 1) /
        (n - m + 2 : ℝ) ^ 2)
  else 0

/-- The summed lower-allocation source weight, expressed on the ordered
coordinate list. -/
def transportLowerAllocationSum {n : ℕ} (I : Fin n → Fin 2)
    (C_f C_g R ρ s : ℝ) : ℝ :=
  ((directionalSplitsNonempty (List.ofFn I)).map fun p =>
    if 2 ≤ p.1.length then
      C_f * p.1.length.factorial * R ^ p.1.length /
          (p.1.length + 1 : ℝ) ^ 2 *
        (16 * C_g * s * (p.2.length + 1).factorial * ρ ^ (p.2.length + 1) /
          (p.2.length + 2 : ℝ) ^ 2)
    else 0).sum

/-- Regrouping the lower source allocations by their right-hand order gives
the binomial sum in the transport proof. -/
theorem transportLowerAllocationSum_eq_binomial {n : ℕ}
    (hn : 2 ≤ n) (I : Fin n → Fin 2)
    (C_f C_g R ρ s : ℝ) :
    transportLowerAllocationSum I C_f C_g R ρ s =
      (∑ k ∈ Finset.range (n - 1 : ℕ),
        (n.choose k : ℝ) *
          (C_f * (n - k).factorial * R ^ (n - k) /
              (n - k + 1 : ℝ) ^ 2 *
            (16 * C_g * s * (k + 1).factorial * ρ ^ (k + 1) /
              (k + 2 : ℝ) ^ 2))) := by
  let L := List.ofFn I
  let alloc := directionalSplitsNonempty L
  let w : ℕ → ℝ := fun m => transportLowerAllocationWeight n m C_f C_g R ρ s
  have hmap : alloc.map (fun p =>
      if 2 ≤ p.1.length then
        C_f * p.1.length.factorial * R ^ p.1.length /
            (p.1.length + 1 : ℝ) ^ 2 *
          (16 * C_g * s * (p.2.length + 1).factorial * ρ ^ (p.2.length + 1) /
            (p.2.length + 2 : ℝ) ^ 2)
      else 0) = alloc.map (fun p => w p.1.length) := by
    apply List.map_congr_left
    intro p hp
    have hlen := directionalSplitsNonempty_length_sum L p hp
    have hmpos := directionalSplitsNonempty_left_pos L p hp
    have hL : L.length = n := by simp [L]
    have hlen' : p.1.length + p.2.length = n := by rw [← hL]; exact hlen
    have hmle : p.1.length ≤ n := by omega
    have hq : p.2.length = n - p.1.length := by
      have hlen' : p.1.length + p.2.length = n := by simpa [L] using hlen
      omega
    by_cases hm : 2 ≤ p.1.length
    · simp [w, transportLowerAllocationWeight, hm, hq, Nat.cast_sub hmle]
    · simp [w, transportLowerAllocationWeight, hm]
  have hleft :
      transportLowerAllocationSum I C_f C_g R ρ s =
        (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) * w (j + 1)) := by
    change (alloc.map (fun p =>
      if 2 ≤ p.1.length then
        C_f * p.1.length.factorial * R ^ p.1.length /
            (p.1.length + 1 : ℝ) ^ 2 *
          (16 * C_g * s * (p.2.length + 1).factorial * ρ ^ (p.2.length + 1) /
            (p.2.length + 2 : ℝ) ^ 2)
      else 0)).sum = _
    calc
      _ = (alloc.map (fun p => w p.1.length)).sum := congrArg List.sum hmap
      _ = _ := by
        simpa [alloc, L, w] using directionalSplitsNonempty_weight_sum L w
  have hzero : w 1 = 0 := by simp [w, transportLowerAllocationWeight]
  have hreflect :
      (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) * w (j + 1)) =
        ∑ k ∈ Finset.range (n - 1 : ℕ),
          (n.choose k : ℝ) * w (n - k) := by
    have hn1 : 1 ≤ n := by omega
    let f : ℕ → ℝ := fun j => (n.choose j : ℝ) * w j
    have hsplit :
        (∑ j ∈ Finset.range n, f (j + 1)) =
          (∑ j ∈ Finset.range (n - 1), f (j + 2)) + f 1 := by
      rw [show n = (n - 1) + 1 by omega, Finset.sum_range_succ']
      simp [f]
    have hreflect :
        (∑ j ∈ Finset.range (n - 1), f (j + 2)) =
          ∑ k ∈ Finset.range (n - 1), f (n - k) := by
      calc
        _ = ∑ k ∈ Finset.range (n - 1), f ((n - 1) - 1 - k + 2) := by
          rw [← Finset.sum_range_reflect (fun j => f (j + 2)) (n - 1)]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt : k < n - 1 := Finset.mem_range.mp hk
          congr 1
          omega
    rw [hsplit]
    simp only [f, hzero, mul_zero, add_zero]
    rw [hreflect]
    simp only [f]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.choose_symm (by
      have hklt : k < n - 1 := Finset.mem_range.mp hk
      omega)]
  rw [hleft, hreflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < n - 1 := Finset.mem_range.mp hk
  have hle : k ≤ n := by omega
  have hsum : n - (n - k) = k := Nat.sub_sub_self hle
  have hcastSub : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hle]
  have hcastComplement : (n : ℝ) - ((n : ℝ) - (k : ℝ)) = (k : ℝ) := by
    ring
  have hnk : 2 ≤ n - k := by omega
  have hw : w (n - k) = C_f * (n - k).factorial * R ^ (n - k) /
      (n - k + 1 : ℝ) ^ 2 *
        (16 * C_g * s * (k + 1).factorial * ρ ^ (k + 1) /
          (k + 2 : ℝ) ^ 2) := by
    simp [w, transportLowerAllocationWeight, hnk, hsum, hcastSub,
      hcastComplement]
  rw [hw]

/-- A time-independent majorant for the lower-allocation source at times
`s ≤ T` and radii `ρ ≤ ρmax`. -/
def transportLowerAllocationMajorant (n : ℕ) (C_f C_g R ρmax T : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n - 1 : ℕ),
    (n.choose k : ℝ) *
      (C_f * (n - k).factorial * R ^ (n - k) /
          (n - k + 1 : ℝ) ^ 2 *
        (16 * C_g * T * (k + 1).factorial * ρmax ^ (k + 1) /
          (k + 2 : ℝ) ^ 2))

theorem transportLowerAllocationSum_le_majorant {n : ℕ} (hn : 2 ≤ n)
    (I : Fin n → Fin 2) {C_f C_g R ρ s T ρmax : ℝ}
    (hCf : 0 ≤ C_f) (hCg : 0 ≤ C_g) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hsT : s ≤ T) (hρ : 0 ≤ ρ) (hρmax : ρ ≤ ρmax) :
    transportLowerAllocationSum I C_f C_g R ρ s ≤
      transportLowerAllocationMajorant n C_f C_g R ρmax T := by
  rw [transportLowerAllocationSum_eq_binomial hn I C_f C_g R ρ s]
  unfold transportLowerAllocationMajorant
  apply Finset.sum_le_sum
  intro k hk
  have htime : 16 * C_g * s ≤ 16 * C_g * T :=
    mul_le_mul_of_nonneg_left hsT (by positivity)
  have hpow : ρ ^ (k + 1) ≤ ρmax ^ (k + 1) :=
    pow_le_pow_left₀ hρ hρmax (k + 1)
  have hcoeff : 0 ≤ (n.choose k : ℝ) := by positivity
  have hleft : 0 ≤ C_f * (n - k).factorial * R ^ (n - k) /
      (n - k + 1 : ℝ) ^ 2 := by positivity
  have hfactor : 0 ≤ ((k + 1).factorial : ℝ) := by positivity
  have hfactorT : 0 ≤ 16 * C_g * T * (k + 1).factorial := by positivity
  have hden : 0 < (k + 2 : ℝ) ^ 2 := by positivity
  have hinner :
      16 * C_g * s * (k + 1).factorial * ρ ^ (k + 1) /
          (k + 2 : ℝ) ^ 2 ≤
        16 * C_g * T * (k + 1).factorial * ρmax ^ (k + 1) /
          (k + 2 : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      16 * C_g * s * (k + 1).factorial * ρ ^ (k + 1) ≤
          16 * C_g * T * (k + 1).factorial * ρ ^ (k + 1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right htime hfactor) (by positivity)
      _ ≤ 16 * C_g * T * (k + 1).factorial * ρmax ^ (k + 1) := by
            exact mul_le_mul_of_nonneg_left hpow hfactorT
  calc
    _ = (n.choose k : ℝ) *
        (C_f * (n - k).factorial * R ^ (n - k) /
          (n - k + 1 : ℝ) ^ 2 *
          (16 * C_g * s * (k + 1).factorial * ρ ^ (k + 1) /
            (k + 2 : ℝ) ^ 2)) := rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinner hleft) hcoeff

/-- The equal-radius transport scale on the forward time interval. -/
def transportShiftRadius (C_f R t : ℝ) : ℝ :=
  R + 8 * t * C_f * R ^ 2

theorem transportShiftRadius_lower {C_f R t : ℝ}
    (ht : 0 ≤ t) (hCf : 0 ≤ C_f) :
    R ≤ transportShiftRadius C_f R t := by
  unfold transportShiftRadius
  apply le_add_of_nonneg_right
  positivity

theorem transportShiftRadius_upper {C_f R t : ℝ}
    (hCf : 0 < C_f) (hR : 0 < R)
    (hT : t ≤ 1 / (8 * C_f * R)) :
    transportShiftRadius C_f R t ≤ 2 * R := by
  have htime : 8 * t * C_f * R ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * C_f * R)).mp hT
    nlinarith [h]
  unfold transportShiftRadius
  nlinarith [htime]

theorem transportLowerAllocationMajorant_nonneg {n : ℕ}
    {C_f C_g R ρ T : ℝ} (hCf : 0 ≤ C_f) (hCg : 0 ≤ C_g)
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (hT : 0 ≤ T) :
    0 ≤ transportLowerAllocationMajorant n C_f C_g R ρ T := by
  unfold transportLowerAllocationMajorant
  apply Finset.sum_nonneg
  intro k hk
  positivity

theorem transportField_lipschitz_of_snorm_one
    {b : ℝ → Vec 2 → Vec 2} {C_f R : ℝ}
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (hCf : 0 ≤ C_f) (hR : 0 < R)
    (hB : ∀ t, snorm (b t) 1 R ≤ ENNReal.ofReal C_f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖ := by
  let L : ℝ := 2 * C_f * R / 4
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K : ℝ≥0 := ⟨L, hL⟩
  have hslice (t : ℝ) : ContDiff ℝ 1 (b t) := by
    have hpair : ContDiff ℝ 1 (fun x : Vec 2 => (t, x)) := by fun_prop
    simpa [Function.uncurry, Function.comp_def] using
      (hb.of_le (by norm_num : (1 : ℕ) ≤ ∞)).comp hpair
  have hD (t : ℝ) (x : Vec 2) : ‖fderiv ℝ (b t) x‖ ≤ L := by
    have h := fderiv_norm_le_of_snorm_one_le (b t) (hslice t) hR hCf (hB t) x
    simpa [L] using h
  have hD' (t : ℝ) (x : Vec 2) : ‖fderiv ℝ (b t) x‖₊ ≤ K := by
    exact_mod_cast hD t x
  refine ⟨L, hL, ?_⟩
  intro t x y
  have hLip : LipschitzWith K (b t) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hslice t).differentiable (by norm_num))
      (hD' t)
  have h := (hLip.dist_le_mul x y)
  change dist (b t x) (b t y) ≤ L * dist x y at h
  simpa [dist_eq_norm] using h

/-- The differentiated transport source is bounded by a linear top-order jet
term and a finite lower-order forcing, using the equal-radius induction
hypothesis on `[-T,T]`. -/
theorem transportSourceArray_norm_le_of_lower_bounds {n : ℕ} (hn : 2 ≤ n)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {C_f C_g R T : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g)
    (hR : 0 < R) (hT : 0 ≤ T) (hTmax : T ≤ 1 / (8 * C_f * R))
    (hB : ∀ t m, 1 ≤ m → m ≤ n →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t, snorm (g t) n R ≤ ENNReal.ofReal C_g)
    (hLower : ∀ k, 1 ≤ k → k < n → ∀ t, |t| ≤ T →
      snorm (Y t) k (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|)) :
    ∀ t, |t| ≤ T → ∀ x,
      ‖transportSpatialSourceArray n b g Y t x‖ ≤
        ((n : ℝ) * C_f * R / 2) *
            ‖orderedSpatialJetArray n (Y t) x‖ +
          (C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
            2 * transportLowerAllocationMajorant n C_f C_g R (2 * R) T) := by
  intro t ht x
  let A : ℝ → ℕ → ℝ := fun s _ => 16 * C_g * |s|
  let RY : ℝ → ℝ := fun s => transportShiftRadius C_f R |s|
  let F : ℝ := C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
    2 * transportLowerAllocationMajorant n C_f C_g R (2 * R) T
  have hA : ∀ s k, 0 ≤ A s k := by
    intro s k
    dsimp [A]
    positivity
  have hRY : ∀ s, 0 < RY s := by
    intro s
    dsimp [RY, transportShiftRadius]
    positivity
  have hYbound : ∀ s, |s| ≤ T → ∀ k, 1 ≤ k → k < n →
      snorm (Y s) k (RY s) ≤ ENNReal.ofReal (A s k) := by
    intro s hs k hkpos hklt
    simpa [A, RY] using hLower k hkpos hklt s hs
  have hMajorant :
      0 ≤ transportLowerAllocationMajorant n C_f C_g R (2 * R) T :=
    transportLowerAllocationMajorant_nonneg hCf.le hCg hR.le
      (by positivity) hT
  have hF : 0 ≤ F := by
    dsimp [F]
    positivity
  have htop (I : Fin n → Fin 2) :
      ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
          b g Y (t, x)‖ ≤
        C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          2 * ((n : ℝ) * (C_f * R / 4 *
              ‖orderedSpatialJetArray n (Y t) x‖) +
            transportLowerAllocationMajorant n C_f C_g R (2 * R) T) := by
    have hU : ∀ J : Fin n → Fin 2,
        ‖orderedPartial n (Y t) x J‖ ≤
          ‖orderedSpatialJetArray n (Y t) x‖ := by
      intro J
      exact norm_le_pi_norm _ J
    have hlocal := transportSourceJet_coordinate_norm_le_local I
      hb hg hY.smooth (RY := RY) hR (fun s => hRY s) hCf.le hCg A hA
      hB hG hYbound t ht x hU
    have hlow : transportLowerAllocationSum I C_f C_g R
        (transportShiftRadius C_f R |t|) |t| ≤
          transportLowerAllocationMajorant n C_f C_g R (2 * R) T := by
      apply transportLowerAllocationSum_le_majorant hn I hCf.le hCg hR.le hT
      · exact ht
      · exact (hRY t).le
      · exact transportShiftRadius_upper hCf hR (le_trans ht hTmax)
    have hlocal' :
        ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
            b g Y (t, x)‖ ≤
          C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
            2 * ((n : ℝ) * (C_f * R / 4 *
                ‖orderedSpatialJetArray n (Y t) x‖) +
              transportLowerAllocationSum I C_f C_g R
                (transportShiftRadius C_f R |t|) |t|) := by
      simpa [transportLowerAllocationSum, transportLowerAllocationWeight,
        A, RY, transportShiftRadius] using hlocal
    exact hlocal'.trans (by nlinarith [hlow])
  rw [pi_norm_le_iff_of_nonempty]
  intro I
  have hcoord := htop I
  change ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
      b g Y (t, x)‖ ≤
    ((n : ℝ) * C_f * R / 2) * ‖orderedSpatialJetArray n (Y t) x‖ +
      (C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
        2 * transportLowerAllocationMajorant n C_f C_g R (2 * R) T)
  calc
    _ ≤ C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          2 * ((n : ℝ) * (C_f * R / 4 *
            ‖orderedSpatialJetArray n (Y t) x‖) +
            transportLowerAllocationMajorant n C_f C_g R (2 * R) T) := hcoord
    _ = ((n : ℝ) * C_f * R / 2) *
          ‖orderedSpatialJetArray n (Y t) x‖ +
          (C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
            2 * transportLowerAllocationMajorant n C_f C_g R (2 * R) T) := by ring

/-- The sharp differentiated source estimate in binomial order. This is the
form whose time integral gives the corrected coefficient and the corrected
shifted convolution. -/
theorem transportSourceJet_norm_le_sharp {n : ℕ} (hn : 2 ≤ n)
    (I : Fin n → Fin 2) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {C_f C_g R T U : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g)
    (hR : 0 < R)
    (hB : ∀ t m, 1 ≤ m → m ≤ n →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t, snorm (g t) n R ≤ ENNReal.ofReal C_g)
    (hLower : ∀ k, 1 ≤ k → k < n → ∀ t, |t| ≤ T →
      snorm (Y t) k (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|))
    (t : ℝ) (ht : |t| ≤ T) (x : Vec 2)
    (hUjet : ∀ J : Fin n → Fin 2,
      ‖orderedPartial n (Y t) x J‖ ≤ U) :
    ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
        b g Y (t, x)‖ ≤
      C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
        ((n : ℝ) * C_f * R / 2) * U +
        2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
          (n.choose k : ℝ) *
            (C_f * (n - k).factorial * R ^ (n - k) /
                (n - k + 1 : ℝ) ^ 2 *
              (16 * C_g * |t| * (k + 1).factorial *
                transportShiftRadius C_f R |t| ^ (k + 1) /
                (k + 2 : ℝ) ^ 2))) := by
  let A : ℝ → ℕ → ℝ := fun s _ => 16 * C_g * |s|
  let RY : ℝ → ℝ := fun s => transportShiftRadius C_f R |s|
  have hA : ∀ s k, 0 ≤ A s k := by
    intro s k
    dsimp [A]
    positivity
  have hRY : ∀ s, 0 < RY s := by
    intro s
    dsimp [RY, transportShiftRadius]
    positivity
  have hYbound : ∀ s, |s| ≤ T → ∀ k, 1 ≤ k → k < n →
      snorm (Y s) k (RY s) ≤ ENNReal.ofReal (A s k) := by
    intro s hs k hkpos hklt
    simpa [A, RY] using hLower k hkpos hklt s hs
  have hlocal := transportSourceJet_coordinate_norm_le_local I
    hb hg hY.smooth (RY := RY) hR (fun s => hRY s) hCf.le hCg A hA
    hB hG hYbound t ht x hUjet
  have hlocal' :
      ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
          b g Y (t, x)‖ ≤
        C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          2 * ((n : ℝ) * (C_f * R / 4 * U) +
            transportLowerAllocationSum I C_f C_g R
              (transportShiftRadius C_f R |t|) |t|) := by
    simpa [transportLowerAllocationSum, transportLowerAllocationWeight,
      A, RY, transportShiftRadius] using hlocal
  rw [transportLowerAllocationSum_eq_binomial hn I C_f C_g R
    (transportShiftRadius C_f R |t|) |t|] at hlocal'
  calc
    _ ≤ C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          2 * ((n : ℝ) * (C_f * R / 4 * U) +
            (∑ k ∈ Finset.range (n - 1 : ℕ),
              (n.choose k : ℝ) *
                (C_f * (n - k).factorial * R ^ (n - k) /
                    (n - k + 1 : ℝ) ^ 2 *
                  (16 * C_g * |t| * (k + 1).factorial *
                    transportShiftRadius C_f R |t| ^ (k + 1) /
                    (k + 2 : ℝ) ^ 2)))) := hlocal'
    _ = C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
          ((n : ℝ) * C_f * R / 2) * U +
          2 * (∑ k ∈ Finset.range (n - 1 : ℕ),
            (n.choose k : ℝ) *
              (C_f * (n - k).factorial * R ^ (n - k) /
                  (n - k + 1 : ℝ) ^ 2 *
                (16 * C_g * |t| * (k + 1).factorial *
                  transportShiftRadius C_f R |t| ^ (k + 1) /
                  (k + 2 : ℝ) ^ 2))) := by ring

/-- The normalized coordinate-jet ratios used in the a-priori finiteness
step and the sharp absorption. -/
def transportJetRatioSet {n : ℕ} (Y : ℝ → Vec 2 → Vec 2)
    (C_f R T : ℝ) : Set ℝ :=
  {z | ∃ t, 0 < |t| ∧ |t| ≤ T ∧ ∃ I : Fin n → Fin 2, ∃ x : Vec 2,
    z = ‖orderedPartial n (Y t) x I‖ /
      (|t| * (n.factorial *
        transportShiftRadius C_f R |t| ^ n / (n + 1 : ℝ) ^ 2))}

theorem transportJetRatioSet_bddAbove {n : ℕ}
    (Y : ℝ → Vec 2 → Vec 2) {C_f R T D : ℝ}
    (hCf : 0 ≤ C_f) (hR : 0 < R) (hD : 0 ≤ D)
    (hpoint : ∀ t, |t| ≤ T → ∀ I : Fin n → Fin 2, ∀ x,
      ‖orderedPartial n (Y t) x I‖ ≤ |t| * D) :
    BddAbove (transportJetRatioSet (n := n) Y C_f R T) := by
  refine ⟨D / (n.factorial * R ^ n / (n + 1 : ℝ) ^ 2), ?_⟩
  intro z hz
  rcases hz with ⟨t, htpos, htT, I, x, rfl⟩
  let scale : ℝ := n.factorial *
    transportShiftRadius C_f R |t| ^ n / (n + 1 : ℝ) ^ 2
  let scale0 : ℝ := n.factorial * R ^ n / (n + 1 : ℝ) ^ 2
  have hrad : R ≤ transportShiftRadius C_f R |t| :=
    transportShiftRadius_lower (abs_nonneg t) hCf
  have hpow : R ^ n ≤ transportShiftRadius C_f R |t| ^ n :=
    pow_le_pow_left₀ hR.le hrad n
  have hfact : 0 ≤ (n.factorial : ℝ) := by positivity
  have hden : 0 < (n + 1 : ℝ) ^ 2 := by positivity
  have hscaleLower : scale0 ≤ scale := by
    dsimp [scale0, scale]
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_left hpow hfact
  have hscale0 : 0 < scale0 := by dsimp [scale0]; positivity
  have hscale : 0 < scale := lt_of_lt_of_le hscale0 hscaleLower
  have hpoint' := hpoint t htT I x
  have hratio :
      ‖orderedPartial n (Y t) x I‖ / (|t| * scale) ≤ D / scale := by
    calc
      _ ≤ (|t| * D) / (|t| * scale) :=
        div_le_div_of_nonneg_right hpoint' (mul_nonneg (abs_nonneg t) hscale.le)
      _ = D / scale := by field_simp [ne_of_gt htpos]
  have hupper : D / scale ≤ D / scale0 :=
    div_le_div_of_nonneg_left hD hscale0 hscaleLower
  simpa [scale, scale0] using hratio.trans hupper

/-- All order-`n` coordinate partials evolve as one finite-dimensional ODE
along a flow characteristic. -/
theorem orderedSpatialJetArray_hasDerivAt_alongFlow
    {n : ℕ} {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    HasDerivAt
      (fun r => orderedSpatialJetArray n (Y r) (X r x s))
      (transportSpatialSourceArray n b g Y t (X t x s)) t := by
  apply hasDerivAt_pi.mpr
  intro I
  let V := List.ofFn fun j : Fin n => coordinateVector 2 (I j)
  have hchar := transportIteratedSpatialJet_hasDerivAt_alongFlow
    V hY hb hg hX x s t
  have heq :
      (fun r => orderedSpatialJetArray n (Y r) (X r x s) I) =
        (fun r => transportSpatialJet V (Function.uncurry Y) (r, X r x s)) := by
    funext r
    exact (transportSpatialJet_coordinate_eq_orderedPartial I Y hY.smooth
      r (X r x s)).symm
  have hcoord := hchar.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => congrFun heq r)
  simpa [transportSpatialSourceArray, V] using hcoord

/-- The initial value of every positive-order coordinate-jet array is zero. -/
theorem orderedSpatialJetArray_initial_zero
    {n : ℕ} (hn : 0 < n) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y) (x : Vec 2) :
    orderedSpatialJetArray n (Y 0) x = 0 := by
  funext I
  let V := List.ofFn fun j : Fin n => coordinateVector 2 (I j)
  change orderedPartial n (Y 0) x I = 0
  rw [← transportSpatialJet_coordinate_eq_orderedPartial I Y hY.smooth 0 x]
  exact transportSpatialJet_initial_zero_of_nonempty V (by
    intro h
    have : V.length = 0 := by rw [h]; simp
    simp [V] at this
    omega) hY x

/-- Uniform linear source control for the order-`n` jet gives a pointwise
Gronwall bound at every spatial endpoint. -/
theorem orderedSpatialJet_norm_le_gronwall_forward
    {n : ℕ} (hn : 0 < n) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hLip : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {t L F : ℝ} (ht : 0 ≤ t)
    (hsource : ∀ r ∈ Set.Ico 0 t, ∀ x,
      ‖transportSpatialSourceArray n b g Y r x‖ ≤
        L * ‖orderedSpatialJetArray n (Y r) x‖ + F)
    (y : Vec 2) :
    ‖orderedSpatialJetArray n (Y t) y‖ ≤ gronwallBound 0 L F t := by
  let x : Vec 2 := X 0 y t
  let J : ℝ → ((Fin n → Fin 2) → Vec 2) :=
    fun r => orderedSpatialJetArray n (Y r) (X r x 0)
  have hJderiv (r : ℝ) : HasDerivAt J
      (transportSpatialSourceArray n b g Y r (X r x 0)) r := by
    simpa [J] using orderedSpatialJetArray_hasDerivAt_alongFlow
      hY hb hg hX x 0 r
  have hJcont : ContinuousOn J (Set.Icc 0 t) :=
    HasDerivAt.continuousOn (fun r _ => hJderiv r)
  have hJwithin : ∀ r ∈ Set.Ico 0 t,
      HasDerivWithinAt J
        (transportSpatialSourceArray n b g Y r (X r x 0)) (Set.Ici r) r := by
    intro r hr
    exact (hJderiv r).hasDerivWithinAt
  have hinitial : J 0 = 0 := by
    dsimp [J]
    rw [show X 0 x 0 = x by exact hX.1 x 0]
    exact orderedSpatialJetArray_initial_zero hn hY x
  have hbound : ∀ r ∈ Set.Ico 0 t,
      ‖transportSpatialSourceArray n b g Y r (X r x 0)‖ ≤ L * ‖J r‖ + F := by
    intro r hr
    simpa [J] using hsource r hr (X r x 0)
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (δ := 0) (K := L) (ε := F) (a := 0) (b := t)
    hJcont hJwithin (by rw [hinitial]; simp) hbound
  have hendpoint : X t (X 0 y t) 0 = y := by
    calc
      X t (X 0 y t) 0 = X t y t :=
        AVenhance.Infra.Flow.flow_group_law b hLip hX y t 0 t
      _ = y := hX.1 y t
  have hJt : J t = orderedSpatialJetArray n (Y t) y := by
    simp [J, x, hendpoint]
  rw [← hJt]
  simpa using hgron t ⟨ht, le_rfl⟩

/-- The finite-dimensional jet Gronwall estimate for either sign of the
target time. The source hypothesis is only needed on the symmetric interval
`[-T,T]`. -/
theorem orderedSpatialJet_norm_le_gronwall_abs
    {n : ℕ} (hn : 0 < n) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hLip : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {T L F : ℝ}
    (hsource : ∀ r, |r| ≤ T → ∀ x,
      ‖transportSpatialSourceArray n b g Y r x‖ ≤
        L * ‖orderedSpatialJetArray n (Y r) x‖ + F)
    (y : Vec 2) {t : ℝ} (ht : |t| ≤ T) :
    ‖orderedSpatialJetArray n (Y t) y‖ ≤ gronwallBound 0 L F |t| := by
  by_cases htime : 0 ≤ t
  · have hsource' : ∀ r ∈ Set.Ico 0 t, ∀ x,
        ‖transportSpatialSourceArray n b g Y r x‖ ≤
          L * ‖orderedSpatialJetArray n (Y r) x‖ + F := by
      intro r hr x
      have hrnonneg : 0 ≤ r := hr.1
      have hrt : r ≤ T := le_trans (le_of_lt hr.2)
        (by simpa [abs_of_nonneg htime] using ht)
      have hrabs : |r| ≤ T := by simpa [abs_of_nonneg hrnonneg] using hrt
      exact hsource r hrabs x
    simpa [abs_of_nonneg htime] using
      orderedSpatialJet_norm_le_gronwall_forward hn hY hb hg hX hLip htime
        hsource' y
  · have htime' : t ≤ 0 := le_of_not_ge htime
    let τ : ℝ := -t
    let x : Vec 2 := X 0 y t
    let J : ℝ → ((Fin n → Fin 2) → Vec 2) :=
      fun r => orderedSpatialJetArray n (Y (-r)) (X (-r) x 0)
    have hJderiv (r : ℝ) : HasDerivAt J
        (-transportSpatialSourceArray n b g Y (-r) (X (-r) x 0)) r := by
      have hbase := orderedSpatialJetArray_hasDerivAt_alongFlow (n := n)
        hY hb hg hX x 0 (-r)
      have hneg : HasDerivAt (fun q : ℝ => -q) (-1) r :=
        hasDerivAt_neg r
      have hcomp := hbase.scomp r hneg
      simpa [J, Function.comp_def, mul_comm] using hcomp
    have hJcont : ContinuousOn J (Set.Icc 0 τ) :=
      HasDerivAt.continuousOn (fun r _ => hJderiv r)
    have hJwithin : ∀ r ∈ Set.Ico 0 τ,
        HasDerivWithinAt J
          (-transportSpatialSourceArray n b g Y (-r) (X (-r) x 0))
          (Set.Ici r) r := by
      intro r hr
      exact (hJderiv r).hasDerivWithinAt
    have hinitial : J 0 = 0 := by
      dsimp [J]
      simp only [neg_zero]
      rw [show X 0 x 0 = x by exact hX.1 x 0]
      exact orderedSpatialJetArray_initial_zero hn hY x
    have hbound : ∀ r ∈ Set.Ico 0 τ,
        ‖-transportSpatialSourceArray n b g Y (-r) (X (-r) x 0)‖ ≤
          L * ‖J r‖ + F := by
      intro r hr
      have hrnonneg : 0 ≤ r := hr.1
      have hrt : r ≤ τ := le_of_lt hr.2
      have htimeBound : |-r| ≤ T := by
        rw [abs_neg, abs_of_nonneg hrnonneg]
        have hτ : τ = |t| := by simp [τ, abs_of_nonpos htime']
        calc
          r ≤ τ := hrt
          _ = |t| := hτ
          _ ≤ T := ht
      have h := hsource (-r) htimeBound (X (-r) x 0)
      simpa [J, norm_neg] using h
    have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := 0) (K := L) (ε := F) (a := 0) (b := τ)
      hJcont hJwithin (by rw [hinitial]; simp) hbound
    have hendpoint : X t (X 0 y t) 0 = y := by
      calc
        X t (X 0 y t) 0 = X t y t :=
          AVenhance.Infra.Flow.flow_group_law b hLip hX y t 0 t
        _ = y := hX.1 y t
    have hJτ : J τ = orderedSpatialJetArray n (Y t) y := by
      simp [J, τ, x, hendpoint]
    have hτnonneg : 0 ≤ τ := by dsimp [τ]; linarith
    simpa [hJτ, τ, abs_of_nonpos htime'] using
      hgron τ ⟨hτnonneg, le_rfl⟩

theorem transportJetArray_coarse_bound {n : ℕ} (hn : 2 ≤ n)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f C_g R T : ℝ} (hCf : 0 < C_f) (hCg : 0 ≤ C_g)
    (hR : 0 < R) (hT : 0 ≤ T) (hTmax : T ≤ 1 / (8 * C_f * R))
    (hB : ∀ t m, 1 ≤ m → m ≤ n →
      snorm (b t) m R ≤ ENNReal.ofReal C_f)
    (hG : ∀ t, snorm (g t) n R ≤ ENNReal.ofReal C_g)
    (hLower : ∀ k, 1 ≤ k → k < n → ∀ t, |t| ≤ T →
      snorm (Y t) k (transportShiftRadius C_f R |t|) ≤
        ENNReal.ofReal (16 * C_g * |t|)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |t| ≤ T → ∀ x,
      ‖orderedSpatialJetArray n (Y t) x‖ ≤ M := by
  let K : ℝ := (n : ℝ) * C_f * R / 2
  let F : ℝ := C_g * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 +
    2 * transportLowerAllocationMajorant n C_f C_g R (2 * R) T
  let M : ℝ := gronwallBound 0 K F T
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hMajorant :
      0 ≤ transportLowerAllocationMajorant n C_f C_g R (2 * R) T :=
    transportLowerAllocationMajorant_nonneg hCf.le hCg hR.le
      (by positivity) hT
  have hF : 0 ≤ F := by
    dsimp [F]
    exact add_nonneg (by positivity) (mul_nonneg (by norm_num) hMajorant)
  have hLip := transportField_lipschitz_of_snorm_one hb hCf.le hR
    (fun t => hB t 1 (by omega) (by omega))
  have hsource := transportSourceArray_norm_le_of_lower_bounds hn
    hY hb hg hCf hCg hR hT hTmax hB hG hLower
  rcases hLip with ⟨Llip, _, hLipFun⟩
  have hmono := gronwallBound_mono (show 0 ≤ (0 : ℝ) by norm_num) hF hK
  have hM : 0 ≤ M := by
    have h := hmono hT
    simpa [M, gronwallBound] using h
  refine ⟨M, hM, ?_⟩
  intro t ht x
  have hnpos : 0 < n := by omega
  have hJ := orderedSpatialJet_norm_le_gronwall_abs hnpos hY hb hg hX ⟨Llip, hLipFun⟩
    hsource x ht
  have hmonotone : gronwallBound 0 K F |t| ≤ M := by
    simpa [M] using hmono ht
  exact hJ.trans hmonotone

theorem transportOrderedPartial_norm_le_symmetric_source_bound
    {n : ℕ} (hn : 0 < n) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hLip : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {T D : ℝ}
    (hsource : ∀ t, |t| ≤ T → ∀ I : Fin n → Fin 2, ∀ x,
      ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
        b g Y (t, x)‖ ≤ D)
    {t : ℝ} (ht : |t| ≤ T) (I : Fin n → Fin 2) (x : Vec 2) :
    ‖orderedPartial n (Y t) x I‖ ≤ |t| * D := by
  let V := List.ofFn fun j => coordinateVector 2 (I j)
  have hV : V ≠ [] := by
    intro hnil
    have hlen : V.length = 0 := by rw [hnil]; rfl
    simp [V] at hlen
    omega
  have hchar := transportSolution_spatialJet_intervalIntegral V hV hY hb hg hX
    (X 0 x t) t
  have hendpoint : X t (X 0 x t) 0 = x := by
    calc
      X t (X 0 x t) 0 = X t x t :=
        AVenhance.Infra.Flow.flow_group_law b hLip hX x t 0 t
      _ = x := hX.1 x t
  have hcoord := transportSpatialJet_coordinate_eq_orderedPartial I Y
    hY.smooth t x
  have hformula : orderedPartial n (Y t) x I =
      ∫ r in 0..t,
        transportSourceJet V b g Y (r, X r (X 0 x t) 0) := by
    rw [hendpoint] at hchar
    rw [← hcoord]
    exact hchar
  by_cases htime : 0 ≤ t
  · have hbound : ∀ r ∈ Set.uIoc 0 t,
        ‖transportSourceJet V b g Y (r, X r (X 0 x t) 0)‖ ≤ D := by
      intro r hr
      have hr' : r ∈ Set.Ioc 0 t := by
        simpa [Set.uIoc_of_le htime] using hr
      have hrabs : |r| ≤ T := by
        rw [abs_of_nonneg hr'.1.le]
        calc
          r ≤ t := hr'.2
          _ ≤ |t| := le_abs_self t
          _ ≤ T := ht
      exact hsource r hrabs I (X r (X 0 x t) 0)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    calc
      _ = ‖∫ r in 0..t,
            transportSourceJet V b g Y (r, X r (X 0 x t) 0)‖ := by rw [hformula]
      _ ≤ D * |t - 0| := hint
      _ = |t| * D := by rw [sub_zero]; ring
  · have htime' : t ≤ 0 := le_of_not_ge htime
    let τ : ℝ := -t
    let F : ℝ → Vec 2 := fun r =>
      transportSourceJet V b g Y (r, X r (X 0 x t) 0)
    have hτ : τ = |t| := by simp [τ, abs_of_nonpos htime']
    have hsub : (∫ s in 0..τ, F (-s)) = (∫ r in t..0, F r) := by
      simpa [F, τ] using
        (intervalIntegral.integral_comp_neg (f := F) (a := (0 : ℝ)) (b := τ))
    have hnegformula :
        (∫ r in 0..t, F r) = -∫ s in 0..τ, F (-s) := by
      calc
        (∫ r in 0..t, F r) = -∫ r in t..0, F r := by
          rw [intervalIntegral.integral_symm]
        _ = -∫ s in 0..τ, F (-s) := by rw [← hsub]
    have hτnonneg : 0 ≤ τ := by rw [hτ]; exact abs_nonneg t
    have hbound : ∀ s ∈ Set.uIoc 0 τ,
        ‖F (-s)‖ ≤ D := by
      intro s hs
      have hs' : s ∈ Set.Ioc 0 τ := by
        simpa [Set.uIoc_of_le hτnonneg] using hs
      have hsT : s ≤ T := by
        calc
          s ≤ τ := hs'.2
          _ = |t| := hτ
          _ ≤ T := ht
      have htimeBound : |-s| ≤ T := by
        rw [abs_neg, abs_of_nonneg hs'.1.le]
        exact hsT
      exact hsource (-s) htimeBound I (X (-s) (X 0 x t) 0)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hpositive :
        ‖∫ s in 0..τ, F (-s)‖ ≤ D * |τ - 0| := hint
    calc
      _ = ‖∫ r in 0..t, F r‖ := by rw [hformula]
      _ = ‖-∫ s in 0..τ, F (-s)‖ := by rw [hnegformula]
      _ = ‖∫ s in 0..τ, F (-s)‖ := norm_neg _
      _ ≤ D * |τ - 0| := hpositive
      _ = |t| * D := by rw [sub_zero, abs_of_nonneg hτnonneg, hτ]; ring

theorem transportOrderedPartial_norm_le_integrated_source_bound
    {n : ℕ} (hn : 0 < n) {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hLip : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖)
    {T t : ℝ} (ht : |t| ≤ T) (B : ℝ → ℝ) (hBcont : Continuous B)
    (hsource : ∀ r, |r| ≤ T → ∀ I : Fin n → Fin 2, ∀ x,
      ‖transportSourceJet (List.ofFn fun j => coordinateVector 2 (I j))
        b g Y (r, x)‖ ≤ B |r|)
    (I : Fin n → Fin 2) (x : Vec 2) :
    ‖orderedPartial n (Y t) x I‖ ≤ ∫ s in 0..|t|, B s := by
  let V := List.ofFn fun j => coordinateVector 2 (I j)
  have hV : V ≠ [] := by
    intro hnil
    have hlen : V.length = 0 := by rw [hnil]; rfl
    simp [V] at hlen
    omega
  have hchar := transportSolution_spatialJet_intervalIntegral V hV hY hb hg hX
    (X 0 x t) t
  have hendpoint : X t (X 0 x t) 0 = x := by
    calc
      X t (X 0 x t) 0 = X t x t :=
        AVenhance.Infra.Flow.flow_group_law b hLip hX x t 0 t
      _ = x := hX.1 x t
  have hcoord := transportSpatialJet_coordinate_eq_orderedPartial I Y
    hY.smooth t x
  have hformula : orderedPartial n (Y t) x I =
      ∫ r in 0..t,
        transportSourceJet V b g Y (r, X r (X 0 x t) 0) := by
    rw [hendpoint] at hchar
    rw [← hcoord]
    exact hchar
  have hsourceSmooth : ContDiff ℝ ∞ (transportSourceJet V b g Y) := by
    have hjet := transportSolution_iteratedDirectionalDerivative_isSmoothSolution
      V ⟨hY, hg⟩ hb
    simpa [Function.uncurry_curry] using hjet.source_smooth
  have hflowContinuous (z : Vec 2) : Continuous fun r => X r z 0 := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.2 z 0 r).continuousAt
  let F : ℝ → Vec 2 := fun r =>
    transportSourceJet V b g Y (r, X r (X 0 x t) 0)
  have hFcont : Continuous F := by
    dsimp [F]
    exact hsourceSmooth.continuous.comp
      (continuous_id.prodMk (hflowContinuous (X 0 x t)))
  have hFnorm : IntervalIntegrable (fun r => ‖F r‖) volume 0 t :=
    hFcont.norm.intervalIntegrable 0 t
  have hBint : IntervalIntegrable B volume 0 |t| := hBcont.intervalIntegrable 0 |t|
  by_cases htime : 0 ≤ t
  · have htimeabs : |t| = t := abs_of_nonneg htime
    have hpoint : ∀ r ∈ Set.Icc 0 t, ‖F r‖ ≤ B r := by
      intro r hr
      have hrT : |r| ≤ T := by
        rw [abs_of_nonneg hr.1]
        exact (le_trans hr.2 (le_abs_self t)).trans ht
      simpa [F, abs_of_nonneg hr.1] using
        hsource r hrT I (X r (X 0 x t) 0)
    have hmajor := intervalIntegral.integral_mono_on htime hFnorm
      (by simpa [htimeabs] using hBint) hpoint
    calc
      _ = ‖∫ r in 0..t, F r‖ := by rw [hformula]
      _ ≤ ∫ r in 0..t, ‖F r‖ :=
        intervalIntegral.norm_integral_le_integral_norm htime
      _ ≤ ∫ r in 0..t, B r := hmajor
      _ = ∫ s in 0..|t|, B s := by rw [htimeabs]
  · have htime' : t ≤ 0 := le_of_not_ge htime
    let τ : ℝ := -t
    let G : ℝ → Vec 2 := fun s => F (-s)
    have hτ : τ = |t| := by simp [τ, abs_of_nonpos htime']
    have hsub : (∫ s in 0..τ, G s) = (∫ r in t..0, F r) := by
      simpa [G, F, τ] using
        (intervalIntegral.integral_comp_neg (f := F) (a := (0 : ℝ)) (b := τ))
    have hnegformula : (∫ r in 0..t, F r) = -∫ s in 0..τ, G s := by
      calc
        (∫ r in 0..t, F r) = -∫ r in t..0, F r := by
          rw [intervalIntegral.integral_symm]
        _ = -∫ s in 0..τ, G s := by rw [← hsub]
    have hτnonneg : 0 ≤ τ := by rw [hτ]; exact abs_nonneg t
    have hGcont : Continuous G := hFcont.comp continuous_neg
    have hGnorm : IntervalIntegrable (fun s => ‖G s‖) volume 0 τ :=
      hGcont.norm.intervalIntegrable 0 τ
    have hpoint : ∀ s ∈ Set.Icc 0 τ, ‖G s‖ ≤ B s := by
      intro s hs
      have hsT : s ≤ T := by
        calc
          s ≤ τ := hs.2
          _ = |t| := hτ
          _ ≤ T := ht
      have htimeBound : |-s| ≤ T := by
        rw [abs_neg, abs_of_nonneg hs.1]
        exact hsT
      simpa [G, F, abs_of_nonneg hs.1] using
        hsource (-s) htimeBound I (X (-s) (X 0 x t) 0)
    have hmajor := intervalIntegral.integral_mono_on hτnonneg hGnorm
      (by rw [hτ]; exact hBint) hpoint
    have hBintτ : (∫ s in 0..τ, B s) = ∫ s in 0..|t|, B s := by rw [hτ]
    calc
      _ = ‖∫ r in 0..t, F r‖ := by rw [hformula]
      _ = ‖-∫ s in 0..τ, G s‖ := by rw [hnegformula]
      _ = ‖∫ s in 0..τ, G s‖ := norm_neg _
      _ ≤ ∫ s in 0..τ, ‖G s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hτnonneg
      _ ≤ ∫ s in 0..τ, B s := hmajor
      _ = ∫ s in 0..|t|, B s := hBintτ

/-- A pointwise estimate for every ordered coordinate partial controls the
paper's essential-supremum derivative seminorm. -/
theorem derivativeSup_le_of_orderedPartial_pointwise
    {n : ℕ} (f : Vec 2 → Vec 2) {M : ℝ}
    (hpoint : ∀ I : Fin n → Fin 2, ∀ x,
      ‖orderedPartial n f x I‖ ≤ M) :
    derivativeSup n f ≤ ENNReal.ofReal M := by
  classical
  unfold derivativeSup
  apply iSup_le
  intro I
  unfold partialSup
  exact eLpNormEssSup_le_of_ae_bound <|
    Filter.Eventually.of_forall fun x => by
      exact hpoint I x

end AVenhance.FaaDiBruno

end
