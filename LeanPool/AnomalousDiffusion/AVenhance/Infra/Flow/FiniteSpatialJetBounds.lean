/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetGlobal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearWindowBounds
public import Mathlib.Analysis.ODE.ExistUnique

/-! Uniform trajectory bounds for recursive spatial jets. The base point
component is controlled inductively, and each newly appended column satisfies
a linear equation with coefficients bounded on the resulting compact tube. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

theorem FiniteSpatialJetBounds.norm_prod_pi_le_of_components
    {E : Type*} [NormedAddCommGroup E] (x : E) (f : Fin 2 → E)
    {C : ℝ} (hC : 0 ≤ C) (hx : ‖x‖ ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ‖(x, f)‖ ≤ C := by
  rw [Prod.norm_def]
  apply max_le
  · exact hx
  · have hpi : ‖f‖ ≤ C := by
      have hpiIff : ‖f‖ ≤ C ↔ ∀ i : Fin 2, ‖f i‖ ≤ C :=
        pi_norm_le_iff_of_nonneg (x := f) hC
      exact hpiIff.2 hf
    exact hpi

theorem FiniteSpatialJetBounds.exists_spatialJetField_derivative_bound_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ)
    (a d R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ∈ Icc a d → ∀ z : SpatialJetState n,
      ‖z‖ ≤ R →
      ‖fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, z)‖ ≤ M := by
  let F : ℝ × SpatialJetState n → SpatialJetState n :=
    Function.uncurry (spatialJetField b n)
  have hF : ContDiff ℝ ∞ F := spatialJetField_smooth hb n
  have hDf : Continuous (fun p => fderiv ℝ F p) :=
    hF.continuous_fderiv (by norm_num)
  have hnorm : Continuous (fun p => ‖fderiv ℝ F p‖) := continuous_norm.comp hDf
  let K : Set (ℝ × SpatialJetState n) :=
    Icc a d ×ˢ Metric.closedBall 0 R
  have hKcompact : IsCompact K := by
    exact isCompact_Icc.prod (isCompact_closedBall 0 R)
  have hbounded : BddAbove ((fun p => ‖fderiv ℝ F p‖) '' K) :=
    hKcompact.bddAbove_image hnorm.continuousOn
  let M : ℝ := max (sSup ((fun p => ‖fderiv ℝ F p‖) '' K)) 0
  refine ⟨M, le_max_right _ _, ?_⟩
  intro t ht z hz
  have hmem : ‖fderiv ℝ F (t, z)‖ ∈ (fun p => ‖fderiv ℝ F p‖) '' K :=
    ⟨(t, z), ⟨ht, Metric.mem_closedBall.2 (by simpa [dist_eq_norm] using hz)⟩, rfl⟩
  exact (le_csSup hbounded hmem).trans (le_max_left _ _)

private theorem spatialJetFlow_bounded_on_window_colDeriv1 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
      Vec (2 : ℕ)}
    (hX : IsFlowOn b X) (n : ℕ) (a d s : ℝ),
    let a' : ℝ := min a s - 1;
    let d' : ℝ := max d s + 1;
    let F : ℝ × SpatialJetState n → SpatialJetState n :=
      Function.uncurry (spatialJetField b n);
    ∀ (zbase : SpatialJetState n) (directions : Fin (2 : ℕ) → SpatialJetState n),
      let Ynext := spatialJetFlow hb X hX (n + 1);
      IsFlowOn (spatialJetField b (n + (1 : ℕ))) Ynext →
        (∀ q ∈ Icc a' d', (Ynext q (zbase, directions) s).1 = spatialJetFlow hb X hX n q zbase s) →
          let A : ℝ → SpatialJetState n →L[ℝ] SpatialJetState n := fun q =>
            (fderiv ℝ F (q, spatialJetFlow hb X hX n q zbase s)).comp
              (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n));
          ∀ (i : Fin (2 : ℕ)),
            ∀ q ∈ Icc a' d',
              HasDerivAt (fun (r : ℝ) => (Ynext r (zbase, directions) s).2 i)
                ((A q : SpatialJetState n → SpatialJetState n) ((Ynext q (zbase, directions) s).2
                    i)) q
    := by
  intro b hb X hX n a d s a' d' F zbase directions Ynext hYnext hlowerEq A i q hq
  have hderiv := hYnext.2 (zbase, directions) s q
  let colProj : SpatialJetState (n + 1) →L[ℝ] SpatialJetState n :=
    (ContinuousLinearMap.proj (R := ℝ) i).comp
      (ContinuousLinearMap.snd ℝ (SpatialJetState n)
        (Fin 2 → SpatialJetState n))
  have hprojPoint (z : SpatialJetState (n + 1)) :
      colProj z = z.2 i := by
    change (ContinuousLinearMap.proj (R := ℝ) i) z.2 = z.2 i
    rfl
  have hproj := colProj.hasFDerivAt.comp q hderiv
  have hcoeff :
      ((fderiv ℝ F (q, (Ynext q (zbase, directions) s).1)).comp
        (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) =
        A q := by
    rw [hlowerEq q hq]
  have hcoordEq : (fun r => (Ynext r (zbase, directions) s).2 i) =
      fun r => colProj (Ynext r (zbase, directions) s) := by
    funext r
    symm
    exact hprojPoint (Ynext r (zbase, directions) s)
  have hprojCoord := (hproj.hasDerivAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r => congrFun hcoordEq r))
  have hfieldPoint :
      (spatialJetField b (n + 1) q (Ynext q (zbase, directions) s)).2 i =
        fderiv ℝ F (q, (Ynext q (zbase, directions) s).1)
          (0, (Ynext q (zbase, directions) s).2 i) := by
    simp [spatialJetField, F]
  have hprojVal :
      ((colProj.comp (ContinuousLinearMap.toSpanSingleton ℝ
        (spatialJetField b (n + 1) q (Ynext q (zbase, directions) s)))) 1) =
        fderiv ℝ F (q, (Ynext q (zbase, directions) s).1)
          (0, (Ynext q (zbase, directions) s).2 i) := by
    calc
      _ = colProj (spatialJetField b (n + 1) q
            (Ynext q (zbase, directions) s)) := by simp
      _ = (spatialJetField b (n + 1) q
            (Ynext q (zbase, directions) s)).2 i :=
          hprojPoint _
      _ = _ := hfieldPoint
  have hproj' := hprojCoord.congr_deriv hprojVal
  have hcoeff' :
      fderiv ℝ F (q, (Ynext q (zbase, directions) s).1)
          (0, (Ynext q (zbase, directions) s).2 i) =
        A q ((Ynext q (zbase, directions) s).2 i) := by
    change ((fderiv ℝ F (q, (Ynext q (zbase, directions) s).1)).comp
      (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)))
      ((Ynext q (zbase, directions) s).2 i) = _
    rw [hcoeff]
  rw [hcoeff'] at hproj'
  exact hproj'

private theorem spatialJetFlow_bounded_on_window_Vbound2 :
  ∀ {b : ℝ → Vec (2 : ℕ) → Vec (2 : ℕ)} (hb : SmoothPeriodicField b) {X : ℝ → Vec (2 : ℕ) → ℝ →
      Vec (2 : ℕ)}
    (hX : IsFlowOn b X) (n : ℕ) (a d s R : ℝ),
    let a' : ℝ := min a s - 1;
    let d' : ℝ := max d s + 1;
    s ∈ Icc a' d' →
      ∀ (Cbase : ℝ),
        (∀ t ∈ Icc a' d', ∀ (z : SpatialJetState n), ‖z‖ ≤ R → ‖spatialJetFlow hb X hX n t z s‖ ≤
            Cbase) →
          ∀ (Mraw : ℝ),
            let M : ℝ := max Mraw 0;
            (0 : ℝ) ≤ M →
              (∀ t ∈ Icc a' d',
                  ∀ (y : SpatialJetState n),
                    ‖y‖ ≤ Cbase →
                      ‖fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, y) ∘SL
                            ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)‖ ≤
                        M) →
                let F : ℝ × SpatialJetState n → SpatialJetState n :=
                  Function.uncurry (spatialJetField b n);
                let E : ℝ := Real.exp (M * (d' - a')) * R;
                ∀ (zbase : SpatialJetState n) (directions : Fin (2 : ℕ) → SpatialJetState n),
                  ‖(zbase, directions)‖ ≤ R →
                    ‖zbase‖ ≤ R →
                      let A : ℝ → SpatialJetState n →L[ℝ] SpatialJetState n := fun q =>
                        (fderiv ℝ F (q, spatialJetFlow hb X hX n q zbase s)).comp
                          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n));
                      ∀ (V : ℝ → SpatialJetState n → ℝ → SpatialJetState n),
                        IsFlowOn (fun (t : ℝ) (z : SpatialJetState n) => (A t : SpatialJetState n
                            → SpatialJetState n) z)
                            V →
                          ∀ (i : Fin (2 : ℕ)), ∀ q ∈ Icc a' d', ‖V q (directions i) s‖ ≤ E
    := by
  intro b hb X hX n a d s R a' d' hs' Cbase hCbase Mraw M hM0 hMderiv F E zbase directions hz
      hzbase A V hV i q hq
  have hMglobal : ∀ r, r ∈ Icc a' d' → ‖A r‖ ≤ M := by
    intro r hr
    apply hMderiv r hr (spatialJetFlow hb X hX n r zbase s)
    exact hCbase r hr zbase hzbase
  have hlin := linearFlow_norm_bound_on_window hV hs' hMglobal
    (directions i) q hq
  have htime : |q - s| ≤ d' - a' := by
    apply abs_le.mpr
    constructor <;> dsimp [a', d'] <;>
      linarith [hq.1, hq.2, hs'.1, hs'.2]
  have hexp : Real.exp (M * |q - s|) ≤ Real.exp (M * (d' - a')) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hM0)
  have hdir : ‖directions i‖ ≤ R := by
    calc
      ‖directions i‖ ≤ ‖directions‖ := norm_le_pi_norm directions i
      _ ≤ ‖(zbase, directions)‖ := norm_snd_le (zbase, directions)
      _ ≤ R := hz
  have hfinal : ‖V q (directions i) s‖ ≤
      Real.exp (M * |q - s|) * ‖directions i‖ := hlin
  calc
    ‖V q (directions i) s‖ ≤
        Real.exp (M * |q - s|) * ‖directions i‖ := hfinal
    _ ≤ Real.exp (M * (d' - a')) * R :=
        mul_le_mul hexp hdir (norm_nonneg _) (Real.exp_nonneg _)
    _ = E := rfl

/-- On any compact time window, all order-n jet trajectories from a bounded
set of initial states remain in one bounded state ball. -/
theorem spatialJetFlow_bounded_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X) :
    ∀ n a d s R, 0 ≤ R →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t, t ∈ Icc a d →
        ∀ z : SpatialJetState n, ‖z‖ ≤ R →
          ‖spatialJetFlow hb X hX n t z s‖ ≤ C := by
  intro n
  induction n with
  | zero =>
      intro a d s R hR
      let G : ℝ × Vec 2 → Vec 2 := fun p => X p.1 p.2 s
      have hG : Continuous G := by
        have hXcont := flow_continuous_joint_of_smoothPeriodic hb
          (show AVenhance.IsFlow b X from hX)
        have hmap : Continuous (fun p : ℝ × Vec 2 => (p.1, p.2, s)) := by fun_prop
        exact hXcont.comp hmap
      let K : Set (ℝ × Vec 2) := Icc a d ×ˢ Metric.closedBall 0 R
      have hKcompact : IsCompact K := by
        exact isCompact_Icc.prod (isCompact_closedBall 0 R)
      have hnorm : Continuous (fun p => ‖G p‖) := continuous_norm.comp hG
      have hbounded : BddAbove ((fun p => ‖G p‖) '' K) :=
        hKcompact.bddAbove_image hnorm.continuousOn
      let C : ℝ := max (sSup ((fun p => ‖G p‖) '' K)) 0
      refine ⟨C, le_max_right _ _, ?_⟩
      intro t ht z hz
      have hmem : ‖G (t, z)‖ ∈ (fun p => ‖G p‖) '' K := by
        refine ⟨(t, z), ⟨ht, ?_⟩, rfl⟩
        apply Metric.mem_closedBall.2
        rw [dist_eq_norm, sub_zero]
        exact hz
      change ‖G (t, z)‖ ≤ C
      exact (le_csSup hbounded hmem).trans (le_max_left _ _)
  | succ n ih =>
      intro a d s R hR
      let a' : ℝ := min a s - 1
      let d' : ℝ := max d s + 1
      have ha' : a' ≤ a := by dsimp [a']; linarith [min_le_left a s]
      have hd' : d ≤ d' := by dsimp [d']; linarith [le_max_left d s]
      have hs' : s ∈ Icc a' d' := by
        constructor
        · dsimp [a']
          linarith [min_le_right a s]
        · dsimp [d']
          linarith [le_max_right d s]
      obtain ⟨Cbase, hCbase0, hCbase⟩ := ih a' d' s R hR
      obtain ⟨Mraw, _, hMraw⟩ :=
        FiniteSpatialJetBounds.exists_spatialJetField_derivative_bound_on_window hb n a' d' Cbase
      let M : ℝ := max Mraw 0
      have hM0 : 0 ≤ M := le_max_right _ _
      have hMderiv (t : ℝ) (ht : t ∈ Icc a' d') (y : SpatialJetState n)
          (hy : ‖y‖ ≤ Cbase) :
          ‖(fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, y)).comp
            (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))‖ ≤ M := by
        calc
          _ ≤ ‖fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, y)‖ *
              ‖ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)‖ :=
            (fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, y)).opNorm_comp_le _
          _ = ‖fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, y)‖ := by
            rw [ContinuousLinearMap.norm_inr]
            simp
          _ ≤ Mraw := hMraw t ht y hy
          _ ≤ M := le_max_left _ _
      let F : ℝ × SpatialJetState n → SpatialJetState n :=
        Function.uncurry (spatialJetField b n)
      have hF : ContDiff ℝ ∞ F := spatialJetField_smooth hb n
      have hAcont (z : SpatialJetState n) (u : ℝ) :
          Continuous (fun t : ℝ =>
            (fderiv ℝ F (t, spatialJetFlow hb X hX n t z u)).comp
              (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) := by
        have hDf : Continuous (fun p : ℝ × SpatialJetState n => fderiv ℝ F p) :=
          hF.continuous_fderiv (by norm_num)
        have hcomp : Continuous
            (fun L : (ℝ × SpatialJetState n) →L[ℝ] SpatialJetState n =>
              L.comp (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) := by
          fun_prop
        have hY : Continuous (fun t : ℝ => spatialJetFlow hb X hX n t z u) := by
          apply continuous_iff_continuousAt.mpr
          intro t
          exact (spatialJetFlow_isFlow hb hX n).2 z u t |>.continuousAt
        exact hcomp.comp (hDf.comp (continuous_id.prodMk hY))
      obtain ⟨Ccol, hCcol0, hCcolBound⟩ :
          ∃ Ccol : ℝ, 0 ≤ Ccol ∧ ∀ t, t ∈ Icc a' d' →
            ∀ z : SpatialJetState (n + 1), ‖z‖ ≤ R →
              ‖spatialJetFlow hb X hX (n + 1) t z s‖ ≤ Ccol := by
        let E : ℝ := Real.exp (M * (d' - a')) * R
        have hE0 : 0 ≤ E := by dsimp [E]; positivity
        let Cjet : ℝ := max Cbase E
        have hCjet0 : 0 ≤ Cjet := le_max_of_le_left hCbase0
        refine ⟨Cjet, hCjet0, ?_⟩
        intro t ht z hz
        rcases z with ⟨zbase, directions⟩
        have hzbase : ‖zbase‖ ≤ R := (norm_fst_le (zbase, directions)).trans hz
        have hYlower : IsFlowOn (spatialJetField b n)
            (spatialJetFlow hb X hX n) := spatialJetFlow_isFlow hb hX n
        let Ynext := spatialJetFlow hb X hX (n + 1)
        have hYnext : IsFlowOn (spatialJetField b (n + 1)) Ynext :=
          spatialJetFlow_isFlow hb hX (n + 1)
        let lowerFlow : ℝ → SpatialJetState n → ℝ → SpatialJetState n :=
          fun q y u => (Ynext q (y, directions) u).1
        have hlower : IsFlowOn (spatialJetField b n) lowerFlow := by
          constructor
          · intro y u
            change (Ynext u (y, directions) u).1 = y
            simpa using congrArg Prod.fst (hYnext.1 (y, directions) u)
          · intro y u q
            have hderiv := hYnext.2 (y, directions) u q
            have hproj := (ContinuousLinearMap.fst ℝ (SpatialJetState n)
              (Fin 2 → SpatialJetState n)).hasFDerivAt.comp q hderiv
            change HasDerivAt (fun r => (Ynext r (y, directions) u).1)
              (spatialJetField b n q ((Ynext q (y, directions) u).1)) q at hproj
            exact hproj
        have hlowerEq (q : ℝ) (hq : q ∈ Icc a' d') :
            (Ynext q (zbase, directions) s).1 =
              spatialJetFlow hb X hX n q zbase s := by
          symm
          exact spatialJetField_flow_unique_on_window hb n hYlower hlower
            a' d' s hs' zbase q hq
        let A : ℝ → SpatialJetState n →L[ℝ] SpatialJetState n := fun q =>
          (fderiv ℝ F (q, spatialJetFlow hb X hX n q zbase s)).comp
            (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))
        have hA : Continuous A := hAcont zbase s
        obtain ⟨V, hV⟩ := (existsUnique_linearFlowOn A hA).exists
        have hVbound (i : Fin 2) (q : ℝ) (hq : q ∈ Icc a' d') :
            ‖V q (directions i) s‖ ≤ E := by
          exact @spatialJetFlow_bounded_on_window_Vbound2 b hb X hX n a d s R hs' Cbase hCbase
              Mraw hM0 hMderiv zbase directions hz hzbase V hV i q hq
        have hcolDeriv (i : Fin 2) (q : ℝ) (hq : q ∈ Icc a' d') : HasDerivAt
            (fun r => (Ynext r (zbase, directions) s).2 i)
            (A q ((Ynext q (zbase, directions) s).2 i)) q := by
          exact @spatialJetFlow_bounded_on_window_colDeriv1 b hb X hX n a d s zbase directions
              hYnext hlowerEq i q hq
        have hcurveCont (i : Fin 2) : ContinuousOn
            (fun q => (Ynext q (zbase, directions) s).2 i) (Icc a' d') :=
          HasDerivAt.continuousOn (fun q hq => hcolDeriv i q hq)
        have hVcont (i : Fin 2) : ContinuousOn
            (fun q => V q (directions i) s) (Icc a' d') :=
          HasDerivAt.continuousOn (fun q _ => hV.2 (directions i) s q)
        have hLip : ∀ q ∈ Ioo a' d',
            LipschitzOnWith (Real.toNNReal M)
              (fun v => A q v) Set.univ := by
          intro q hq
          apply LipschitzWith.lipschitzOnWith
          apply LipschitzWith.of_dist_le_mul
          intro u v
          change dist (A q u) (A q v) ≤ (Real.toNNReal M : ℝ) * dist u v
          rw [dist_eq_norm, dist_eq_norm, ← map_sub]
          rw [Real.coe_toNNReal M hM0]
          calc
            ‖A q (u - v)‖ ≤ ‖A q‖ * ‖u - v‖ := (A q).le_opNorm _
            _ ≤ M * ‖u - v‖ := mul_le_mul_of_nonneg_right
              (hMderiv q (Ioo_subset_Icc_self hq)
                (spatialJetFlow hb X hX n q zbase s)
                (hCbase q (Ioo_subset_Icc_self hq) zbase hzbase)) (norm_nonneg _)
        have heqstart (i : Fin 2) :
            (Ynext s (zbase, directions) s).2 i = V s (directions i) s := by
          calc
            (Ynext s (zbase, directions) s).2 i = directions i :=
              congrArg (fun w : SpatialJetState (n + 1) => w.2 i)
                (hYnext.1 (zbase, directions) s)
            _ = V s (directions i) s := by rw [hV.1]
        have hsInterior : s ∈ Ioo a' d' := by
          constructor <;> dsimp [a', d'] <;>
            linarith [min_le_right a s, le_max_right d s]
        have hcol (i : Fin 2) := ODE_solution_unique_of_mem_Icc
          (v := fun q v => A q v) (s := fun _ => Set.univ)
          (K := Real.toNNReal M)
          (f := fun q => (Ynext q (zbase, directions) s).2 i)
          (g := fun q => V q (directions i) s)
          (a := a') (b := d') (t₀ := s)
          hLip hsInterior
          (hcurveCont i) (fun q hq => hcolDeriv i q (Ioo_subset_Icc_self hq))
          (fun _ _ => Set.mem_univ _) (hVcont i)
          (fun q hq => hV.2 (directions i) s q)
          (fun _ _ => Set.mem_univ _) (heqstart i)
        have hbase : ‖(Ynext t (zbase, directions) s).1‖ ≤ Cbase := by
          rw [hlowerEq t ht]
          exact hCbase t ht zbase hzbase
        have hcols (i : Fin 2) : ‖(Ynext t (zbase, directions) s).2 i‖ ≤ E := by
          have hsame := hcol i ht
          change (Ynext t (zbase, directions) s).2 i = V t (directions i) s at hsame
          rw [hsame]
          exact hVbound i t ht
        have hcols' (i : Fin 2) :
            ‖(Ynext t (zbase, directions) s).2 i‖ ≤ Cjet :=
          (hcols i).trans (le_max_right _ _)
        have hstate := FiniteSpatialJetBounds.norm_prod_pi_le_of_components
          (Ynext t (zbase, directions) s).1
          (fun i => (Ynext t (zbase, directions) s).2 i) hCjet0
          (hbase.trans (le_max_left _ _))
          hcols'
        change ‖Ynext t (zbase, directions) s‖ ≤ Cjet
        exact hstate
      refine ⟨Ccol, hCcol0, ?_⟩
      intro t ht z hz
      exact hCcolBound t ⟨le_trans ha' ht.1, le_trans ht.2 hd'⟩ z hz

end

end AVenhance.Infra.Flow
