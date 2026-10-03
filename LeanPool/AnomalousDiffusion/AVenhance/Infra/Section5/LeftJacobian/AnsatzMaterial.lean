/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.SourceHelpers
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TEquationRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenAnsatzMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportIdentities
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientMaterial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixTransport

/-! Source-generic ansatz material equation (corrected form).

The right-hand side of the source transport equation is an arbitrary real `Src`;
nothing about the flux form of the source is used. The proof is a copy of
`frozen_ansatz_material_equation_of_source` with the `hsource'` split dropped. -/

@[expose] public section

noncomputable section

open Homogenization Filter
open scoped Topology

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem AnsatzMaterial.vecDot_spaceGrad_eq_fderiv
    {f : Vec 2 → ℝ} {x : Vec 2} (v : Vec 2) :
    vecDot v (spaceGrad f x) = fderiv ℝ f x v := by
  have hv : v = ∑ i : Fin 2, (v i) • basisVec i := by
    funext i
    fin_cases i <;> simp [basisVec, Fin.sum_univ_two]
  rw [hv]
  unfold vecDot spaceGrad
  simp only [Fin.sum_univ_two, Finset.sum_apply]
  simp [smul_eq_mul]

theorem AnsatzMaterial.jointVector_time_component
    {F : ℝ → Vec 2 → Vec 2} {L : (ℝ × Vec 2) →L[ℝ] Vec 2}
    {t : ℝ} {x : Vec 2}
    (hF : HasFDerivAt (Function.uncurry F) L (t, x)) (j : Fin 2) :
    HasDerivAt (fun s => F s x j) ((L (1, 0)) j) t := by
  let curve : ℝ → ℝ × Vec 2 := fun s => (s, x)
  have hcurve : HasDerivAt curve (1, (0 : Vec 2)) t := by
    exact (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hcomp := hF.comp t hcurve.hasFDerivAt
  have hproj := (ContinuousLinearMap.proj j).hasFDerivAt.comp t hcomp
  have hderiv := hproj.hasDerivAt
  have hEq : (fun s => F s x j) =ᶠ[𝓝 t]
      (fun s => (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ)
        (Function.uncurry F (curve s))) := by
    filter_upwards [] with s
    rfl
  have hderiv' := hderiv.congr_of_eventuallyEq hEq
  have hval :
      ((ContinuousLinearMap.proj j).comp
          (L.comp (ContinuousLinearMap.toSpanSingleton ℝ
            (1, (0 : Vec 2))))) 1 =
        (L (1, 0)) j := by
    simp [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  rw [hval] at hderiv'
  exact hderiv'

theorem AnsatzMaterial.jointVector_space
    {F : ℝ → Vec 2 → Vec 2} {L : (ℝ × Vec 2) →L[ℝ] Vec 2}
    {t : ℝ} {x : Vec 2}
    (hF : HasFDerivAt (Function.uncurry F) L (t, x)) :
    HasFDerivAt (F t)
      (L.comp ((0 : Vec 2 →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (Vec 2)))) x := by
  let slice : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hslice : HasFDerivAt slice
      ((0 : Vec 2 →L[ℝ] ℝ).prod
        (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h := hF.comp x hslice
  simpa [slice, Function.uncurry, Function.comp_def] using h

theorem AnsatzMaterial.chiMK_zero_of_not_odd (κ : ℝ) (m : ℕ) (k : ℤ)
    (t : ℝ) (hk : ¬ Odd k) : I.chiMK κ m k t = fun _ => 0 := by
  have h1 : k % 4 ≠ 1 := by
    intro hmod
    rcases Int.even_or_odd k with he | ho
    · rcases he with ⟨z, hz⟩
      omega
    · exact hk ho
  have h3 : k % 4 ≠ 3 := by
    intro hmod
    rcases Int.even_or_odd k with he | ho
    · rcases he with ⟨z, hz⟩
      omega
    · exact hk ho
  have hu : uShear β I.Λ m k = fun _ => 0 := by
    funext y
    simp [uShear, h1, h3]
  funext y
  change (-(I.corrTime κ m k t)) • uShear β I.Λ m k y = 0
  rw [hu]
  simp

theorem AnsatzMaterial.chiTilde_zero_of_not_odd (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (hk : ¬ Odd k) :
    I.chiTilde hΦ m κ k t = fun _ => 0 := by
  funext x
  change I.chiMK κ m k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) = 0
  rw [AnsatzMaterial.chiMK_zero_of_not_odd I κ m k t hk]

theorem AnsatzMaterial.xiMK_deriv_zero_off_nearSupport
    (m : ℕ) (t ρ : ℝ) (hρ : 0 < ρ) (k : ℤ)
    (hk : k ∉ xiMKNearSupportFinset I m t ρ) :
    deriv (I.xiMK m k) t = 0 := by
  have hlocal : (I.xiMK m k) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      ⟨sub_lt_self t hρ, lt_add_of_pos_right t hρ⟩] with s hs
    by_contra hne
    have hmem : k ∈ xiMKNearSupport I m t ρ := ⟨s, hs, hne⟩
    exact hk ((xiMKNearSupport_finite I m t ρ).mem_toFinset.mpr hmem)
  have hzero : HasDerivAt (I.xiMK m k) 0 t := by
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hlocal
  simpa using hzero.deriv

theorem AnsatzMaterial.finite_odd_sum_eq_tsum
    {S : Finset ℤ} (F : {k : ℤ // Odd k} → ℝ)
    (hzero : ∀ q : {k : ℤ // Odd k}, q.1 ∉ S → F q = 0) :
    (let f : ℤ → ℝ := fun k => if hk : Odd k then F ⟨k, hk⟩ else 0
     ∑ k ∈ S.filter Odd, f k) = ∑' q : {k : ℤ // Odd k}, F q := by
  classical
  let V : Set {k : ℤ // Odd k} := {q | q.1 ∈ S}
  have hV : V.Finite := by
    apply S.finite_toSet.preimage (f := fun q : {k : ℤ // Odd k} => q.1)
    intro q₁ hq₁ q₂ hq₂ heq
    exact Subtype.ext heq
  let U : Finset {k : ℤ // Odd k} := hV.toFinset
  let f : ℤ → ℝ := fun k => if hk : Odd k then F ⟨k, hk⟩ else 0
  have hsum : (∑ k ∈ S.filter Odd, f k) =
      ∑ q ∈ U, F q := by
    refine Finset.sum_bij
      (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : {k : ℤ // Odd k}))
      ?_ ?_ ?_ ?_
    · intro k hk
      exact hV.mem_toFinset.mpr (Finset.mem_filter.mp hk).1
    · intro k₁ hk₁ k₂ hk₂ heq
      exact congrArg Subtype.val heq
    · intro q hq
      have hqV : q ∈ V := hV.mem_toFinset.mp hq
      refine ⟨q.1, Finset.mem_filter.mpr ⟨hqV, q.2⟩, ?_⟩
      exact Subtype.ext rfl
    · intro k hk
      simp [f, (Finset.mem_filter.mp hk).2]
  have htsum : (∑' q : {k : ℤ // Odd k}, F q) = ∑ q ∈ U, F q := by
    apply tsum_eq_sum
    intro q hq
    have hnot : q.1 ∉ S := by
      intro hmem
      have hmemU : q ∈ U := hV.mem_toFinset.mpr hmem
      exact hq hmemU
    exact hzero q hnot
  simpa [f] using hsum.trans htsum.symm

theorem AnsatzMaterial.near_sum_eq_active_odd_support
    (m : ℕ) (hm : 1 ≤ m) (t ρ : ℝ) (hρ : 0 < ρ)
    (F : ℤ → ℝ) (hEven : ∀ k, ¬ Odd k → F k = 0) :
    (∑ k ∈ xiMKNearSupportFinset I m t ρ, I.xiMK m k t * F k) =
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t * F q.1 := by
  classical
  let S := xiMKNearSupportFinset I m t ρ
  let S₀ := (I.xiMK_support_finite m t).toFinset
  let Sodd := S₀.filter Odd
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hSoddSub : Sodd ⊆ S := by
    intro k hk
    have hxi : I.xiMK m k t ≠ 0 :=
      (I.xiMK_support_finite m t).mem_toFinset.mp
        (Finset.mem_filter.mp hk).1
    have htmem : t ∈ Set.Ioo (t - ρ) (t + ρ) := by
      constructor <;> linarith
    exact (xiMKNearSupport_finite I m t ρ).mem_toFinset.mpr ⟨t, htmem, hxi⟩
  have hzero : ∀ k ∈ S, k ∉ Sodd → I.xiMK m k t * F k = 0 := by
    intro k hkS hkoddSupport
    by_cases hodd : Odd k
    · have hxi : I.xiMK m k t = 0 := by
        by_contra hne
        have hmem : k ∈ Sodd := Finset.mem_filter.mpr
          ⟨(I.xiMK_support_finite m t).mem_toFinset.mpr hne, hodd⟩
        exact hkoddSupport hmem
      simp [hxi]
    · simp [hEven k hodd]
  have hfinite :
      (∑ k ∈ S, I.xiMK m k t * F k) =
        ∑ k ∈ Sodd, I.xiMK m k t * F k :=
    (Finset.sum_subset hSoddSub hzero).symm
  have hbridge := xiMK_odd_integer_support_sum_eq_subtype_sum
    I m hm t F
  calc
    _ = ∑ k ∈ Sodd, I.xiMK m k t * F k := hfinite
    _ = ∑ q ∈ U, I.xiMK m q.1 t * F q.1 := by
      simpa [Sodd, U, smul_eq_mul] using hbridge

private theorem variantA_ansatz_material_equation_of_source_sumstep1 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm
    : (1 : ℕ) ≤ m) (κm κprev : ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (t : ℝ) (x : Vec (2 : ℕ)) (ρ :
    ℝ) (LT LH : Vec (2 : ℕ) →L[ℝ] ℝ) (Lχ LG : ℤ → ℝ × Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ)),
  let Tf : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let b : Vec (2 : ℕ) := streamVel (Φ (m - (1 : ℕ))) t x;
  let Near : Finset ℤ := xiMKNearSupportFinset I m t ρ;
  let U : Finset { k : ℤ // Odd k } := (Section3.xiMK_odd_support_finite I hm t).toFinset;
  let J : Vec (2 : ℕ) →L[ℝ] ℝ × Vec (2 : ℕ) := ContinuousLinearMap.prod (0 : Vec (2 : ℕ) →L[ℝ]
    ℝ) (ContinuousLinearMap.id ℝ (Vec (2 : ℕ)));
  let Lχx : ℤ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (k : ℤ) => Lχ k ∘SL J;
  let LGx : ℤ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (k : ℤ) => LG k ∘SL J;
  let χtime : ℤ → Vec (2 : ℕ) := fun (k : ℤ) => (Lχ k : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)) ((1 : ℝ),
    (0 : Vec (2 : ℕ)));
  let Gtime : ℤ → Vec (2 : ℕ) := fun (k : ℤ) => (LG k : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)) ((1 : ℝ),
    (0 : Vec (2 : ℕ)));
  let Fcut : ℤ → ℝ := fun (k : ℤ) => deriv (I.xiMK m k) t * vecDot (I.chiTilde hΦ m κm k t x) (G
    I hΦ m Tf (lIdx β I.Λ m k) t x);
  ∑ k ∈ Near, Fcut k = cutoff1 I hΦ m κm Tf t x →
  let Ftransport : ℤ → ℝ := fun (k : ℤ) => vecDot (fun (j : Fin (2 : ℕ)) => deriv (fun (s : ℝ)
    => I.chiMK κm m k s (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t) (G I hΦ m Tf (lIdx β I.Λ m
    k) t x) + vecDot (I.chiTilde hΦ m κm k t x) ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
    (gradDiv (fun (s : ℝ) (y : Vec (2 : ℕ)) => (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
    (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y) t x));
  ∑ k ∈ Near, I.xiMK m k t * Ftransport k = ∑ q ∈ U, I.xiMK m (↑q : ℤ) t * Ftransport (↑q : ℤ) →
    ∑ k ∈ Near, (Fcut k + I.xiMK m k t * (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
    vecDot (I.chiTilde hΦ m κm k t x) (Gtime k))) + ∑ k ∈ Near, I.xiMK m k t * (vecDot ((Lχx k :
    Vec (2 : ℕ) → Vec (2 : ℕ)) b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) + vecDot (I.chiTilde hΦ m
    κm k t x) ((LGx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b)) = ∑ k ∈ Near, Fcut k + ∑ k ∈ Near, I.xiMK
    m k t * Ftransport k → ∑ k ∈ Near, (Fcut k + I.xiMK m k t * (vecDot (χtime k) (G I hΦ m Tf
    (lIdx β I.Λ m k) t x) + vecDot (I.chiTilde hΦ m κm k t x) (Gtime k))) + ((LT : Vec (2 : ℕ) →
    ℝ) b + ∑ k ∈ Near, I.xiMK m k t * (vecDot ((Lχx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b) (G I hΦ m
    Tf (lIdx β I.Λ m k) t x) + vecDot (I.chiTilde hΦ m κm k t x) ((LGx k : Vec (2 : ℕ) → Vec (2
    : ℕ)) b)) + (LH : Vec (2 : ℕ) → ℝ) b) = cutoff1 I hΦ m κm Tf t x + ∑ q ∈ U, I.xiMK m (↑q :
    ℤ) t * vecDot (fun (j : Fin (2 : ℕ)) => deriv (fun (s : ℝ) => I.chiMK κm m (↑q : ℤ) s
    (I.xFlowInv hΦ m (lIdx β I.Λ m (↑q : ℤ)) t x) j) t) (G I hΦ m Tf (lIdx β I.Λ m (↑q : ℤ)) t
    x) + ∑ q ∈ U, I.xiMK m (↑q : ℤ) t * vecDot (I.chiTilde hΦ m κm (↑q : ℤ) t x) ((I.flowGrad hΦ
    m (lIdx β I.Λ m (↑q : ℤ)) t x).mulVec (gradDiv (fun (s : ℝ) (y : Vec (2 : ℕ)) => (I.Kmat κm
    m s + I.sMat hΦ m κm s y).mulVec (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y)
    t x)) + ((LT : Vec (2 : ℕ) → ℝ) b + (LH : Vec (2 : ℕ) → ℝ) b)
    := by
  intro β I Φ hΦ m hm κm κprev T t x ρ LT LH Lχ LG Tf b Near U J Lχx LGx χtime Gtime Fcut hcutOdd
      Ftransport htransportFinite hmodeSums
  calc
    _ = (∑ k ∈ Near,
          (Fcut k + I.xiMK m k t *
            (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
              vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)))) +
        (∑ k ∈ Near, I.xiMK m k t *
          (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
            vecDot (I.chiTilde hΦ m κm k t x) (LGx k b))) +
        (LT b + LH b) := by
          abel
    _ = ((∑ k ∈ Near, Fcut k) +
        ∑ k ∈ Near, I.xiMK m k t * Ftransport k) +
        (LT b + LH b) := by
          rw [hmodeSums]
    _ = cutoff1 I hΦ m κm Tf t x +
        (∑ q ∈ U, I.xiMK m q.1 t * Ftransport q.1) +
        (LT b + LH b) := by
          rw [hcutOdd, htransportFinite]
    _ = cutoff1 I hΦ m κm Tf t x +
        (∑ q ∈ U, I.xiMK m q.1 t *
          vecDot (fun j => deriv (fun s => I.chiMK κm m q.1 s
            (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m Tf (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ U, I.xiMK m q.1 t *
          vecDot (I.chiTilde hΦ m κm q.1 t x)
            ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
              (gradDiv (fun s y =>
                (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                  (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y)
                t x))) +
        (LT b + LH b) := by
        simp only [Ftransport]
        have hsplit :
            (∑ q ∈ U, I.xiMK m q.1 t *
              (vecDot (fun j => deriv (fun s => I.chiMK κm m q.1 s
                (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
                (G I hΦ m Tf (lIdx β I.Λ m q.1) t x) +
               vecDot (I.chiTilde hΦ m κm q.1 t x)
                ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                  (gradDiv (fun s y =>
                    (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                      (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y)
                    t x)))) =
              (∑ q ∈ U, I.xiMK m q.1 t *
                vecDot (fun j => deriv (fun s => I.chiMK κm m q.1 s
                  (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
                  (G I hΦ m Tf (lIdx β I.Λ m q.1) t x)) +
              (∑ q ∈ U, I.xiMK m q.1 t *
                vecDot (I.chiTilde hΦ m κm q.1 t x)
                  ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                    (gradDiv (fun s y =>
                      (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                        (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y)
                      t x))) := by
          calc
            _ = ∑ q ∈ U, (I.xiMK m q.1 t *
                  vecDot (fun j => deriv (fun s => I.chiMK κm m q.1 s
                    (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
                    (G I hΦ m Tf (lIdx β I.Λ m q.1) t x) +
                  I.xiMK m q.1 t *
                    vecDot (I.chiTilde hΦ m κm q.1 t x)
                      ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                        (gradDiv (fun s y =>
                          (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                            (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y)
                          t x))) := by
                apply Finset.sum_congr rfl
                intro q hq
                ring
            _ = _ := Finset.sum_add_distrib
        rw [hsplit]
        ring

private theorem variantA_ansatz_material_equation_of_source_transportTerm2 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ), (1
    : ℕ) ≤ m → ∀ (κm κprev : ℝ) (θ₀ : Vec (2 : ℕ) → ℝ) (θprev : ℝ → Vec (2 : ℕ) → ℝ) (T : ℕ → ℝ
    → Vec (2 : ℕ) → ℝ), I.IsTIterates hΦ m κm κprev θ₀ θprev T → ∀ (t : ℝ), (0 : ℝ) < t → ∀ (x :
    Vec (2 : ℕ)) (ρ : ℝ) (Lχ LG : ℤ → ℝ × Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ)), (∀ k ∈
    xiMKNearSupportFinset I m t ρ, HasFDerivAt (Function.uncurry fun (s : ℝ) (y : Vec (2 : ℕ))
    => I.chiTilde hΦ m κm k s y) (Lχ k) (t, x)) → (∀ k ∈ xiMKNearSupportFinset I m t ρ,
    HasFDerivAt (Function.uncurry fun (s : ℝ) (y : Vec (2 : ℕ)) => G I hΦ m (T (Nstar β)) (lIdx
    β I.Λ m k) s y) (LG k) (t, x)) →
  let Tf : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let b : Vec (2 : ℕ) := streamVel (Φ (m - (1 : ℕ))) t x;
  let Near : Finset ℤ := xiMKNearSupportFinset I m t ρ;
  let J : Vec (2 : ℕ) →L[ℝ] ℝ × Vec (2 : ℕ) := ContinuousLinearMap.prod (0 : Vec (2 : ℕ) →L[ℝ]
    ℝ) (ContinuousLinearMap.id ℝ (Vec (2 : ℕ)));
  let Lχx : ℤ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (k : ℤ) => Lχ k ∘SL J;
  let LGx : ℤ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (k : ℤ) => LG k ∘SL J;
  let χtime : ℤ → Vec (2 : ℕ) := fun (k : ℤ) => (Lχ k : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)) ((1 : ℝ),
    (0 : Vec (2 : ℕ)));
  let Gtime : ℤ → Vec (2 : ℕ) := fun (k : ℤ) => (LG k : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)) ((1 : ℝ),
    (0 : Vec (2 : ℕ)));
  (∀ k ∈ Near, HasFDerivAt (I.chiTilde hΦ m κm k t) (Lχx k) x) → (∀ k ∈ Near, HasFDerivAt (fun
    (y : Vec (2 : ℕ)) => G I hΦ m Tf (lIdx β I.Λ m k) t y) (LGx k) x) →
  let Ftransport : ℤ → ℝ := fun (k : ℤ) => vecDot (fun (j : Fin (2 : ℕ)) => deriv (fun (s : ℝ)
    => I.chiMK κm m k s (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t) (G I hΦ m Tf (lIdx β I.Λ m
    k) t x) + vecDot (I.chiTilde hΦ m κm k t x) ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
    (gradDiv (fun (s : ℝ) (y : Vec (2 : ℕ)) => (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
    (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y) t x));
  ∀ k ∈ Near, vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) + vecDot (I.chiTilde hΦ m κm k
    t x) (Gtime k) + (vecDot ((Lχx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b) (G I hΦ m Tf (lIdx β I.Λ m
    k) t x) + vecDot (I.chiTilde hΦ m κm k t x) ((LGx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b)) =
    Ftransport k
    := by
  intro β I Φ hΦ m hm κm κprev θ₀ θprev T hT t ht x ρ Lχ LG hχ hG Tf b Near J Lχx LGx χtime Gtime
      hχspace hGspace Ftransport k hk
  have hχmat (j : Fin 2) :
      χtime k j + (Lχx k b) j =
        deriv (fun s => I.chiMK κm m k s
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t := by
    have h := chiTilde_material_transport_component I hΦ m κm k t x j
    rw [(AnsatzMaterial.jointVector_time_component (hχ k hk) j).deriv,
      (hχspace k hk).fderiv] at h
    simpa [χtime, Lχx, J, b] using h
  have hGmat (j : Fin 2) :
      Gtime k j + (LGx k b) j =
        ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
          (gradDiv (fun s y =>
            (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                (spaceGrad (Tf s) y) +
              iterateError I hΦ m κm κprev T s y) t x)) j := by
    have h := final_iterate_pulled_gradient_material_transport I hΦ m hm
      κm κprev θ₀ θprev T hT (lIdx β I.Λ m k) ht x j (hG k hk)
    rw [(AnsatzMaterial.jointVector_time_component (hG k hk) j).deriv,
      (hGspace k hk).fderiv] at h
    simpa [Gtime, LGx, J, b, Tf] using h
  have hχvector : χtime k + Lχx k b =
      fun j => deriv (fun s => I.chiMK κm m k s
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t := by
    funext j
    exact hχmat j
  have hGvector : Gtime k + LGx k b =
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
        (gradDiv (fun s y =>
          (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
              (spaceGrad (Tf s) y) +
            iterateError I hΦ m κm κprev T s y) t x) := by
    funext j
    exact hGmat j
  have hdot :
      (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
        vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)) +
      (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
        vecDot (I.chiTilde hΦ m κm k t x) (LGx k b)) =
      vecDot (χtime k + Lχx k b)
          (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
        vecDot (I.chiTilde hΦ m κm k t x) (Gtime k + LGx k b) := by
    simp [vecDot, Fin.sum_univ_two]
    ring
  calc
    _ = vecDot (χtime k + Lχx k b)
          (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
        vecDot (I.chiTilde hΦ m κm k t x) (Gtime k + LGx k b) := hdot
    _ = Ftransport k := by
      rw [hχvector, hGvector]

private theorem variantA_ansatz_material_equation_of_source_cutOdd3 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm
    : ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (t : ℝ) (x : Vec (2 : ℕ)) (ρ : ℝ), (0 : ℝ) < ρ →
  let Tf : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let Near : Finset ℤ := xiMKNearSupportFinset I m t ρ;
  let Fcut : ℤ → ℝ := fun (k : ℤ) => deriv (I.xiMK m k) t * vecDot (I.chiTilde hΦ m κm k t x) (G
    I hΦ m Tf (lIdx β I.Λ m k) t x);
  (∀ (k : ℤ), ¬Odd k → Fcut k = (0 : ℝ)) → ∑ k ∈ Near, Fcut k = cutoff1 I hΦ m κm Tf t x
    := by
  intro β I Φ hΦ m κm T t x ρ hρ Tf Near Fcut hcutEven
  have hnot : ∑ k ∈ Near.filter (fun k => ¬ Odd k), Fcut k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hcutEven k (Finset.mem_filter.mp hk).2
  have hfilter := Finset.sum_filter_add_sum_filter_not Near Odd Fcut
  have hfiniteOdd := AnsatzMaterial.finite_odd_sum_eq_tsum (S := Near)
    (fun q : {k : ℤ // Odd k} => Fcut q.1)
    (by
      intro q hq
      simp [Fcut, AnsatzMaterial.xiMK_deriv_zero_off_nearSupport I m t ρ hρ q.1 hq])
  calc
    (∑ k ∈ Near, Fcut k) =
        ∑ k ∈ Near.filter Odd, Fcut k := by
          rw [← hfilter, hnot]
          simp
    _ = ∑ k ∈ Near.filter Odd,
          (if hk : Odd k then Fcut k else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_filter] at hk
          simp [hk.2]
    _ = ∑' q : {k : ℤ // Odd k}, Fcut q.1 := by
          simpa [Fcut] using hfiniteOdd
    _ = cutoff1 I hΦ m κm Tf t x := by
          simp [cutoff1, Fcut]

private theorem variantA_ansatz_material_equation_of_source_modeSums4 :
  ∀ {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec (2 : ℕ) → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm
    κprev : ℝ) (T : ℕ → ℝ → Vec (2 : ℕ) → ℝ) (t : ℝ) (x : Vec (2 : ℕ)) (ρ : ℝ) (Lχ LG : ℤ → ℝ ×
    Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ)),
  let Tf : ℝ → Vec (2 : ℕ) → ℝ := T (Nstar β);
  let b : Vec (2 : ℕ) := streamVel (Φ (m - (1 : ℕ))) t x;
  let Near : Finset ℤ := xiMKNearSupportFinset I m t ρ;
  let J : Vec (2 : ℕ) →L[ℝ] ℝ × Vec (2 : ℕ) := ContinuousLinearMap.prod (0 : Vec (2 : ℕ) →L[ℝ]
    ℝ) (ContinuousLinearMap.id ℝ (Vec (2 : ℕ)));
  let Lχx : ℤ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (k : ℤ) => Lχ k ∘SL J;
  let LGx : ℤ → Vec (2 : ℕ) →L[ℝ] Vec (2 : ℕ) := fun (k : ℤ) => LG k ∘SL J;
  let χtime : ℤ → Vec (2 : ℕ) := fun (k : ℤ) => (Lχ k : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)) ((1 : ℝ),
    (0 : Vec (2 : ℕ)));
  let Gtime : ℤ → Vec (2 : ℕ) := fun (k : ℤ) => (LG k : ℝ × Vec (2 : ℕ) → Vec (2 : ℕ)) ((1 : ℝ),
    (0 : Vec (2 : ℕ)));
  let Fcut : ℤ → ℝ := fun (k : ℤ) => deriv (I.xiMK m k) t * vecDot (I.chiTilde hΦ m κm k t x) (G
    I hΦ m Tf (lIdx β I.Λ m k) t x);
  let Ftransport : ℤ → ℝ := fun (k : ℤ) => vecDot (fun (j : Fin (2 : ℕ)) => deriv (fun (s : ℝ)
    => I.chiMK κm m k s (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t) (G I hΦ m Tf (lIdx β I.Λ m
    k) t x) + vecDot (I.chiTilde hΦ m κm k t x) ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
    (gradDiv (fun (s : ℝ) (y : Vec (2 : ℕ)) => (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
    (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y) t x));
  (∀ k ∈ Near, vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) + vecDot (I.chiTilde hΦ m κm
    k t x) (Gtime k) + (vecDot ((Lχx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b) (G I hΦ m Tf (lIdx β I.Λ
    m k) t x) + vecDot (I.chiTilde hΦ m κm k t x) ((LGx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b)) =
    Ftransport k) → ∑ k ∈ Near, (Fcut k + I.xiMK m k t * (vecDot (χtime k) (G I hΦ m Tf (lIdx β
    I.Λ m k) t x) + vecDot (I.chiTilde hΦ m κm k t x) (Gtime k))) + ∑ k ∈ Near, I.xiMK m k t *
    (vecDot ((Lχx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) + vecDot
    (I.chiTilde hΦ m κm k t x) ((LGx k : Vec (2 : ℕ) → Vec (2 : ℕ)) b)) = ∑ k ∈ Near, Fcut k + ∑
    k ∈ Near, I.xiMK m k t * Ftransport k
    := by
  intro β I Φ hΦ m κm κprev T t x ρ Lχ LG Tf b Near J Lχx LGx χtime Gtime Fcut Ftransport
      htransportTerm
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ k ∈ Near,
        (Fcut k + I.xiMK m k t * Ftransport k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hpt :
              (Fcut k + I.xiMK m k t *
                (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
                  vecDot (I.chiTilde hΦ m κm k t x) (Gtime k))) +
              I.xiMK m k t *
                (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
                  vecDot (I.chiTilde hΦ m κm k t x) (LGx k b)) =
              Fcut k + I.xiMK m k t * Ftransport k := by
            calc
              _ = Fcut k + I.xiMK m k t *
                  ((vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
                    vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)) +
                   (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
                    vecDot (I.chiTilde hΦ m κm k t x) (LGx k b))) := by ring
              _ = Fcut k + I.xiMK m k t * Ftransport k := by
                rw [htransportTerm k hk]
          exact hpt
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Source-generic ansatz material equation: the source transport equation for
`T_{m-1}+H_m` may have an arbitrary real right-hand side `Src`, which appears
unchanged in the material derivative of the ansatz. -/
theorem variantA_ansatz_material_equation_of_source
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (LT LH : Vec 2 →L[ℝ] ℝ)
    (hTtime : HasDerivAt (fun s => T (Nstar β) s x)
      (deriv (fun s => T (Nstar β) s x) t) t)
    (hHtime : HasDerivAt (fun s => I.Hm hΦ m κm (T (Nstar β)) s x)
      (deriv (fun s => I.Hm hΦ m κm (T (Nstar β)) s x) t) t)
    (hξ : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasDerivAt (I.xiMK m k) (deriv (I.xiMK m k) t) t)
    (hTx : HasFDerivAt (T (Nstar β) t) LT x)
    (hHx : HasFDerivAt (I.Hm hΦ m κm (T (Nstar β)) t) LH x)
    (Lχ LG : ℤ → (ℝ × Vec 2) →L[ℝ] Vec 2)
    (hχ : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasFDerivAt (Function.uncurry fun s y => I.chiTilde hΦ m κm k s y)
        (Lχ k) (t, x))
    (hG : ∀ k ∈ xiMKNearSupportFinset I m t ρ,
      HasFDerivAt (Function.uncurry fun s y =>
        G I hΦ m (T (Nstar β)) (lIdx β I.Λ m k) s y) (LG k) (t, x))
    (Src : ℝ)
    (hsource :
      deriv (fun s => T (Nstar β) s x) t +
          vecDot (streamVel (Φ (m - 1)) t x)
            (spaceGrad (T (Nstar β) t) x) +
        deriv (fun s => I.Hm hΦ m κm (T (Nstar β)) s x) t +
          fderiv ℝ (I.Hm hΦ m κm (T (Nstar β)) t) x
            (streamVel (Φ (m - 1)) t x) =
      Src) :
    deriv (fun s => I.ansatz hΦ m κm (T (Nstar β)) s x) t +
        vecDot (streamVel (Φ (m - 1)) t x)
          (spaceGrad (I.ansatz hΦ m κm (T (Nstar β)) t) x) =
      cutoff1 I hΦ m κm (T (Nstar β)) t x +
        (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
          I.xiMK m q.1 t * vecDot
            (fun j => deriv (fun s => I.chiMK κm m q.1 s
              (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
            (G I hΦ m (T (Nstar β)) (lIdx β I.Λ m q.1) t x)) +
        (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
          I.xiMK m q.1 t * vecDot (I.chiTilde hΦ m κm q.1 t x)
            ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
              (gradDiv (fun s y =>
                (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                    (spaceGrad (T (Nstar β) s) y) +
                  iterateError I hΦ m κm κprev T s y) t x))) +
        Src := by
  classical
  let Tf : ℝ → Vec 2 → ℝ := T (Nstar β)
  let H : ℝ → Vec 2 → ℝ := I.Hm hΦ m κm Tf
  let b : Vec 2 := streamVel (Φ (m - 1)) t x
  let Near := xiMKNearSupportFinset I m t ρ
  let U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 :=
    (0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))
  let Lχx : ℤ → Vec 2 →L[ℝ] Vec 2 := fun k => (Lχ k).comp J
  let LGx : ℤ → Vec 2 →L[ℝ] Vec 2 := fun k => (LG k).comp J
  let χtime : ℤ → Vec 2 := fun k => Lχ k (1, 0)
  let Gtime : ℤ → Vec 2 := fun k => LG k (1, 0)
  have hχspace : ∀ k ∈ Near,
      HasFDerivAt (I.chiTilde hΦ m κm k t) (Lχx k) x := by
    intro k hk
    simpa [Lχx, J, Function.uncurry] using
      (AnsatzMaterial.jointVector_space (hχ k hk))
  have hGspace : ∀ k ∈ Near,
      HasFDerivAt (fun y => G I hΦ m Tf (lIdx β I.Λ m k) t y)
        (LGx k) x := by
    intro k hk
    simpa [LGx, J, Function.uncurry] using
      (AnsatzMaterial.jointVector_space (hG k hk))
  have hχtime : ∀ k ∈ Near,
      HasDerivAt (fun s => I.chiTilde hΦ m κm k s x) (χtime k) t := by
    intro k hk
    let curve : ℝ → ℝ × Vec 2 := fun s => (s, x)
    have hcurve : HasDerivAt curve (1, (0 : Vec 2)) t := by
      exact (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have hcomp := (hχ k hk).comp t hcurve.hasFDerivAt
    have hval : (Lχ k ∘SL ContinuousLinearMap.toSpanSingleton ℝ (1, (0 : Vec 2))) 1 =
        Lχ k (1, 0) := by simp [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply]
    have hderiv := hcomp.hasDerivAt
    have hfun : (fun s => I.chiTilde hΦ m κm k s x) =ᶠ[𝓝 t]
        (fun s => Function.uncurry (fun r y => I.chiTilde hΦ m κm k r y)
          (curve s)) := by
      filter_upwards [] with s
      rfl
    have hderiv' := hderiv.congr_of_eventuallyEq hfun
    rw [hval] at hderiv'
    exact hderiv'
  have hGtime : ∀ k ∈ Near,
      HasDerivAt (fun s => G I hΦ m Tf (lIdx β I.Λ m k) s x)
        (Gtime k) t := by
    intro k hk
    let Gk : ℝ → Vec 2 → Vec 2 := fun s y =>
      G I hΦ m Tf (lIdx β I.Λ m k) s y
    let curve : ℝ → ℝ × Vec 2 := fun s => (s, x)
    have hcurve : HasDerivAt curve (1, (0 : Vec 2)) t := by
      exact (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have hcomp := (hG k hk).comp t hcurve.hasFDerivAt
    have hval : (LG k ∘SL ContinuousLinearMap.toSpanSingleton ℝ (1, (0 : Vec 2))) 1 =
        LG k (1, 0) := by simp [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.toSpanSingleton_apply]
    have hderiv := hcomp.hasDerivAt
    have hfun : (fun s => Gk s x) =ᶠ[𝓝 t]
        (fun s => Function.uncurry Gk (curve s)) := by
      filter_upwards [] with s
      rfl
    have hderiv' := hderiv.congr_of_eventuallyEq hfun
    rw [hval] at hderiv'
    simpa [Gk] using hderiv'
  have hExpanded := frozen_ansatz_material_expansion I hΦ m κm Tf ρ t x b
      (deriv (fun s => Tf s x) t) (deriv (fun s => H s x) t)
      (fun k => deriv (I.xiMK m k) t) χtime Gtime LT LH Lχx LGx hρ
      hTtime hHtime hξ hχtime hGtime hTx hHx hχspace hGspace
  have hdir : fderiv ℝ (I.ansatz hΦ m κm Tf t) x b =
      vecDot b (spaceGrad (I.ansatz hΦ m κm Tf t) x) := by
    rw [fderiv_scalar_eq_sum_spaceGrad]
    simp [vecDot]
  rw [hdir] at hExpanded
  let Fcut : ℤ → ℝ := fun k => deriv (I.xiMK m k) t *
    vecDot (I.chiTilde hΦ m κm k t x)
      (G I hΦ m Tf (lIdx β I.Λ m k) t x)
  have hcutEven : ∀ k, ¬ Odd k → Fcut k = 0 := by
    intro k hk
    simp [Fcut, AnsatzMaterial.chiTilde_zero_of_not_odd I hΦ m κm k t hk,
      vecDot, Fin.sum_univ_two]
  have hcutOdd :
      (∑ k ∈ Near, Fcut k) = cutoff1 I hΦ m κm Tf t x := by
    exact @variantA_ansatz_material_equation_of_source_cutOdd3 β I Φ hΦ m κm T t x ρ hρ hcutEven
  let Ftransport : ℤ → ℝ := fun k =>
    vecDot (fun j => deriv (fun s => I.chiMK κm m k s
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t)
        (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
      vecDot (I.chiTilde hΦ m κm k t x)
        ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
          (gradDiv (fun s y =>
            (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                (spaceGrad (Tf s) y) +
              iterateError I hΦ m κm κprev T s y) t x))
  have htransportEven : ∀ k, ¬ Odd k → Ftransport k = 0 := by
    intro k hk
    have hχzero := AnsatzMaterial.chiTilde_zero_of_not_odd I hΦ m κm k t hk
    have hbaseZero :
        (fun s => I.chiMK κm m k s
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) = fun _ => 0 := by
      funext s
      exact congrFun (AnsatzMaterial.chiMK_zero_of_not_odd I κm m k s hk) _
    have hbaseCoord (j : Fin 2) :
        deriv (fun s => I.chiMK κm m k s
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) t = 0 := by
      have heq : (fun s => I.chiMK κm m k s
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j) = fun _ => 0 := by
        funext s
        exact congrArg (fun v : Vec 2 => v j)
          (congrFun hbaseZero s)
      rw [heq]
      simp
    simp [Ftransport, hχzero, hbaseCoord, vecDot, Fin.sum_univ_two]
  have htransportFinite :
      (∑ k ∈ Near, I.xiMK m k t * Ftransport k) =
        ∑ q ∈ U, I.xiMK m q.1 t * Ftransport q.1 :=
    AnsatzMaterial.near_sum_eq_active_odd_support I m hm t ρ hρ Ftransport htransportEven
  have htransportTerm (k : ℤ) (hk : k ∈ Near) :
      (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
        vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)) +
      (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
        vecDot (I.chiTilde hΦ m κm k t x) (LGx k b)) =
      Ftransport k := by
    exact @variantA_ansatz_material_equation_of_source_transportTerm2 β I Φ hΦ m hm κm κprev θ₀
        θprev T hT t ht x ρ Lχ LG hχ hG hχspace hGspace k hk
  have hmodeSums :
      (∑ k ∈ Near,
        (Fcut k + I.xiMK m k t *
          (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
            vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)))) +
      ∑ k ∈ Near, I.xiMK m k t *
        (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
          vecDot (I.chiTilde hΦ m κm k t x) (LGx k b)) =
      (∑ k ∈ Near, Fcut k) + ∑ k ∈ Near, I.xiMK m k t * Ftransport k := by
    exact @variantA_ansatz_material_equation_of_source_modeSums4 β I Φ hΦ m κm κprev T t x ρ Lχ LG
        htransportTerm
  have hsource' :
      deriv (fun s => Tf s x) t + deriv (fun s => H s x) t +
        LT b + LH b = Src := by
    have hsrc := hsource
    rw [AnsatzMaterial.vecDot_spaceGrad_eq_fderiv (f := Tf t) (x := x)
      (streamVel (Φ (m - 1)) t x)] at hsrc
    rw [hTx.fderiv, hHx.fderiv] at hsrc
    dsimp [Tf, H, b] at hsrc ⊢
    linear_combination hsrc
  have hExpanded' :
      deriv (fun s => I.ansatz hΦ m κm Tf s x) t +
          vecDot (streamVel (Φ (m - 1)) t x)
            (spaceGrad (I.ansatz hΦ m κm Tf t) x) =
        deriv (fun s => Tf s x) t + deriv (fun s => H s x) t +
          (∑ k ∈ Near,
            (Fcut k + I.xiMK m k t *
              (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
                vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)))) +
          (LT b +
            (∑ k ∈ Near, I.xiMK m k t *
              (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
                vecDot (I.chiTilde hΦ m κm k t x) (LGx k b))) + LH b) := by
    simpa [Tf, H, Near, χtime, Gtime, Fcut, b] using hExpanded
  have hsumstep :
      (∑ k ∈ Near,
        (Fcut k + I.xiMK m k t *
          (vecDot (χtime k) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
            vecDot (I.chiTilde hΦ m κm k t x) (Gtime k)))) +
        (LT b +
          ∑ k ∈ Near, I.xiMK m k t *
            (vecDot (Lχx k b) (G I hΦ m Tf (lIdx β I.Λ m k) t x) +
              vecDot (I.chiTilde hΦ m κm k t x) (LGx k b)) + LH b) =
        cutoff1 I hΦ m κm Tf t x +
          (∑ q ∈ U, I.xiMK m q.1 t *
            vecDot (fun j => deriv (fun s => I.chiMK κm m q.1 s
              (I.xFlowInv hΦ m (lIdx β I.Λ m q.1) t x) j) t)
              (G I hΦ m Tf (lIdx β I.Λ m q.1) t x)) +
          (∑ q ∈ U, I.xiMK m q.1 t *
            vecDot (I.chiTilde hΦ m κm q.1 t x)
              ((I.flowGrad hΦ m (lIdx β I.Λ m q.1) t x).mulVec
                (gradDiv (fun s y =>
                  (I.Kmat κm m s + I.sMat hΦ m κm s y).mulVec
                    (spaceGrad (Tf s) y) + iterateError I hΦ m κm κprev T s y)
                  t x))) +
          (LT b + LH b) := by
    exact @variantA_ansatz_material_equation_of_source_sumstep1 β I Φ hΦ m hm κm κprev T t x ρ LT
        LH Lχ LG hcutOdd htransportFinite hmodeSums
  linear_combination hExpanded' + hsumstep + hsource'

end AVenhance.Infra.Section5.LeftJacobian

end
