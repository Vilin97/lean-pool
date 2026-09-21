/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# From continuous coordinate derivatives to a Frechet derivative

This file supplies the finite-dimensional calculus bridge used by the
Euclidean heat-kernel development.  A function on `Fin n → ℝ` whose packaged
coordinate derivatives exist everywhere and vary continuously has that
package as its genuine Frechet derivative.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Continuous coordinate derivatives on finite real coordinate space
assemble to the genuine Frechet derivative. -/
theorem hasFDerivAt_of_continuous_coordinate_derivatives
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (f : (Fin n → ℝ) → F)
    (D : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] F))
    (hD : Continuous D)
    (hcoord : ∀ x k, HasFDerivAt (fun a => f (Function.update x k a))
      (ContinuousLinearMap.toSpanSingleton ℝ (D x (Pi.single k 1))) (x k)) :
    ∀ x, HasFDerivAt f (D x) x := by
  induction n with
  | zero =>
      intro x
      have hf : f = fun _ => f x := by
        funext y
        rw [Subsingleton.elim y x]
      have hDx : D x = 0 := by
        ext v
        have hv : v = 0 := Subsingleton.elim v 0
        simpa [hv] using (D x).map_zero
      rw [hf, hDx]
      exact hasFDerivAt_const (f x) x
  | succ n ih =>
      intro x
      let V := Fin n → ℝ
      let eL : (ℝ × V) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
        { toFun := fun p => Fin.cons p.1 p.2
          map_add' := by
            intro p q
            ext i
            refine Fin.cases ?_ (fun k => ?_) i
            · simp
            · change p.2 k + q.2 k = p.2 k + q.2 k
              rfl
          map_smul' := by
            intro c p
            ext i
            refine Fin.cases ?_ (fun k => ?_) i
            · simp
            · change c * p.2 k = c * p.2 k
              rfl }
      have heLbij : Function.Bijective eL := by
        constructor
        · intro p q hpq
          apply Prod.ext
          · exact congrFun hpq 0
          · funext k
            exact congrFun hpq k.succ
        · intro y
          refine ⟨(y 0, Fin.tail y), ?_⟩
          exact Fin.cons_self_tail y
      have heLinv : (LinearEquiv.ofBijective eL heLbij).invFun =
          fun y => (y 0, Fin.tail y) := by
        funext y
        apply heLbij.1
        calc
          eL ((LinearEquiv.ofBijective eL heLbij).invFun y) = y :=
            (LinearEquiv.ofBijective eL heLbij).apply_symm_apply y
          _ = eL (y 0, Fin.tail y) := by
            exact (Fin.cons_self_tail y).symm
      let e : (ℝ × V) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
        { toLinearEquiv := LinearEquiv.ofBijective eL heLbij
          continuous_toFun := by
            apply continuous_pi
            intro i
            refine Fin.cases continuous_fst (fun k => ?_) i
            exact (continuous_apply k).comp continuous_snd
          continuous_invFun := by
            have ht : Continuous (fun y : Fin (n + 1) → ℝ =>
                fun k : Fin n => y k.succ) :=
              continuous_pi fun k => continuous_apply k.succ
            rw [heLinv]
            exact (continuous_apply 0).prodMk ht }
      let g : ℝ → V → F := fun a v => f (e (a, v))
      let D₁ : ℝ → V → (ℝ →L[ℝ] F) := fun a v =>
        ContinuousLinearMap.toSpanSingleton ℝ
          (D (e (a, v)) (Pi.single 0 1))
      let D₂ : ℝ → V → (V →L[ℝ] F) := fun a v =>
        ∑ k : Fin n, (ContinuousLinearMap.proj k).smulRight
          (D (e (a, v)) (Pi.single k.succ 1))
      have hD₁ : Continuous ↿D₁ := by
        exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp
          ((hD.comp e.continuous).clm_apply continuous_const)
      have hD₂ : Continuous ↿D₂ := by
        change Continuous (fun p : ℝ × V => ∑ k : Fin n,
          (ContinuousLinearMap.proj k).smulRight
            (D (e p) (Pi.single k.succ 1)))
        simpa using
          (continuous_finsetSum Finset.univ fun k _ =>
            (ContinuousLinearMap.smulRightL ℝ V F
              (ContinuousLinearMap.proj k)).continuous.comp
                ((hD.comp e.continuous).clm_apply continuous_const))
      have hd₁ : ∀ p : ℝ × V, HasFDerivAt (g · p.2) (↿D₁ p) p.1 := by
        intro p
        have hc := hcoord (e p) 0
        convert hc using 1
        · funext a
          apply congrArg f
          ext i
          refine Fin.cases ?_ (fun k => ?_) i
          · simp [g, e, eL, V]
          · simp [g, e, eL, V]
        · rfl
        · simpa [e, eL]
      have hd₂ : ∀ p : ℝ × V, HasFDerivAt (g p.1 ·) (↿D₂ p) p.2 := by
        intro p
        apply ih (g p.1) (D₂ p.1)
        · exact hD₂.comp (continuous_const.prodMk continuous_id)
        · intro v k
          have hc := hcoord (e (p.1, v)) k.succ
          convert hc using 1
          · funext a
            apply congrArg f
            simpa [g, e, eL] using Fin.cons_update p.1 v k a
          · apply congrArg (ContinuousLinearMap.toSpanSingleton ℝ)
            simp [D₂]
          · simpa [e, eL]
      have hg : HasFDerivAt ↿g
          (((↿D₁ (e.symm x)).coprod (↿D₂ (e.symm x)))) (e.symm x) :=
        (hasStrictFDerivAt_uncurry_coprod
          (Eventually.of_forall hd₁) (Eventually.of_forall hd₂)
          hD₁.continuousAt hD₂.continuousAt).hasFDerivAt
      have heinv : HasFDerivAt (fun y : Fin (n + 1) → ℝ => e.symm y)
          e.symm.toContinuousLinearMap x :=
        e.symm.toContinuousLinearMap.hasFDerivAt
      have hout : HasFDerivAt (fun y : Fin (n + 1) → ℝ => ↿g (e.symm y))
          (((↿D₁ (e.symm x)).coprod (↿D₂ (e.symm x))).comp
            e.symm.toContinuousLinearMap) x :=
        hg.comp x heinv
      convert hout using 1
      · funext y
        change f y = f (e (e.symm y))
        rw [e.apply_symm_apply]
      · ext v
        let px := e.symm x
        let pv := e.symm v
        have hex (p : ℝ × V) : e p = Fin.cons p.1 p.2 := rfl
        have hx : e px = x := e.apply_symm_apply x
        have hv : e pv = v := e.apply_symm_apply v
        have hpv0 : pv.1 = v 0 := by
          have h := congrFun hv 0
          simpa only [hex, Fin.cons_zero] using h
        have hpvk : ∀ k : Fin n, pv.2 k = v k.succ := by
          intro k
          have h := congrFun hv k.succ
          simpa only [hex, Fin.cons_succ] using h
        have hdecomp : v = Pi.single 0 (v 0) +
            ∑ k : Fin n, Pi.single k.succ (v k.succ) := by
          ext i
          refine Fin.cases ?_ (fun k => ?_) i
          · simp
          · simp only [Pi.add_apply]
            have hz : (Pi.single 0 (v 0) : Fin (n + 1) → ℝ) k.succ = 0 := by
              simp
            rw [hz, zero_add, Finset.sum_apply]
            rw [Finset.sum_eq_single k]
            · simp
            · intro b _ hbk
              simp [hbk]
            · simp
        have hsingle0 : (Pi.single 0 (v 0) : Fin (n + 1) → ℝ) =
            v 0 • (Pi.single 0 (1 : ℝ) : Fin (n + 1) → ℝ) := by
          ext i
          simp [Pi.single_apply]
        have hsingleSucc : ∀ k : Fin n, Pi.single k.succ (v k.succ) =
            v k.succ • Pi.single k.succ (1 : ℝ) := by
          intro k
          ext i
          simp [Pi.single_apply]
        have hDexpand : (D x) v = v 0 • (D x) (Pi.single 0 1) +
            ∑ k : Fin n, v k.succ • (D x) (Pi.single k.succ 1) := by
          calc
            (D x) v = (D x) (Pi.single 0 (v 0) +
                ∑ k : Fin n, Pi.single k.succ (v k.succ)) :=
              congrArg (D x) hdecomp
            _ = v 0 • (D x) (Pi.single 0 1) +
                ∑ k : Fin n, v k.succ • (D x) (Pi.single k.succ 1) := by
              rw [map_add, map_sum]
              congr 1
              · calc
                  (D x) (Pi.single 0 (v 0)) =
                      (D x) (v 0 • Pi.single 0 1) := congrArg (D x) hsingle0
                  _ = v 0 • (D x) (Pi.single 0 1) := map_smul (D x) _ _
              · apply Finset.sum_congr rfl
                intro k _
                calc
                  (D x) (Pi.single k.succ (v k.succ)) =
                      (D x) (v k.succ • Pi.single k.succ 1) :=
                    congrArg (D x) (hsingleSucc k)
                  _ = v k.succ • (D x) (Pi.single k.succ 1) := map_smul (D x) _ _
        change (D x) v =
          (ContinuousLinearMap.toSpanSingleton ℝ
            (D (e (e.symm x)) (Pi.single 0 1))) pv.1 +
          (∑ k : Fin n, (ContinuousLinearMap.proj k).smulRight
            (D (e (e.symm x)) (Pi.single k.succ 1))) pv.2
        simpa only [e.apply_symm_apply,
          ContinuousLinearMap.toSpanSingleton_apply, hpv0, sum_apply,
          ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.proj_apply, hpvk] using hDexpand

end AnalyticPDE
end RicciFlow
