/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.StrictStatements

namespace V7.Stage6StrictDeterministic

/-- The query selected after a chronological prefix.  At time zero the
frozen strict model requires the supplied initial point. -/
def causalQuery (method : StrictLocalMethod) (t : ℕ)
    (trace : StrictTranscript) : StrictPoint :=
  if t = 0 then method.x0 else method.nextQuery trace

/-- Chronological exact transcript generated against the affine oracle. -/
noncomputable def affineTrace (method : StrictLocalMethod) (eps : ℝ) :
    ℕ → StrictTranscript
  | 0 => []
  | n + 1 =>
      let trace := affineTrace method eps n
      trace ++ [(strictAffineOracle eps method.x0).observe
        (causalQuery method n trace)]

@[simp] theorem affineTrace_zero (method : StrictLocalMethod) (eps : ℝ) :
    affineTrace method eps 0 = [] := rfl

theorem affineTrace_succ (method : StrictLocalMethod) (eps : ℝ) (n : ℕ) :
    affineTrace method eps (n + 1) =
      affineTrace method eps n ++
        [(strictAffineOracle eps method.x0).observe
          (causalQuery method n (affineTrace method eps n))] := rfl

@[simp] theorem affineTrace_length (method : StrictLocalMethod) (eps : ℝ) (n : ℕ) :
    (affineTrace method eps n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [affineTrace_succ, ih]

theorem affineTrace_exact (method : StrictLocalMethod) (eps : ℝ) (n : ℕ) :
    StrictTranscriptExact (strictAffineOracle eps method.x0)
      (affineTrace method eps n) := by
  intro obs hobs
  induction n with
  | zero => simp at hobs
  | succ n ih =>
      rw [affineTrace_succ] at hobs
      simp only [List.mem_append, List.mem_singleton] at hobs
      rcases hobs with hobs | rfl
      · exact ih hobs
      · rfl

theorem affineTrace_take (method : StrictLocalMethod) (eps : ℝ)
    {m n : ℕ} (hmn : m ≤ n) :
    (affineTrace method eps n).take m = affineTrace method eps m := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rfl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · rw [affineTrace_succ, List.take_append_of_le_length]
        · exact ih hmn'
        · simpa using hmn'
      · have hm : m = n + 1 := by omega
        subst m
        simp [affineTrace_succ]

theorem affineTrace_get (method : StrictLocalMethod) (eps : ℝ)
    (n t : ℕ) (ht : t < n) :
    (affineTrace method eps n).get
        ⟨t, by simpa using ht⟩ =
      (strictAffineOracle eps method.x0).observe
        (causalQuery method t (affineTrace method eps t)) := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [affineTrace_succ]
      by_cases htn : t < n
      · change (affineTrace method eps n ++
            [(strictAffineOracle eps method.x0).observe
              (causalQuery method n (affineTrace method eps n))])[t]'
                (by simp [affineTrace_length]; omega) = _
        rw [List.getElem_append_left]
        exact ih htn
      · have hteq : t = n := by omega
        subst t
        change (affineTrace method eps n ++
            [(strictAffineOracle eps method.x0).observe
              (causalQuery method n (affineTrace method eps n))])[n]'
                (by simp [affineTrace_length]) = _
        rw [List.getElem_append_right (by simp [affineTrace_length])]
        simp [affineTrace_length]

theorem affineTrace_runConsistent (method : StrictLocalMethod) (eps : ℝ) (n : ℕ) :
    StrictRunConsistent method (strictAffineOracle eps method.x0)
      (affineTrace method eps n) := by
  refine ⟨affineTrace_exact method eps n, ?_⟩
  intro t ht
  rw [affineTrace_length] at ht
  rw [affineTrace_get method eps n t ht]
  simp only [O3.PairOracle.observe]
  change causalQuery method t (affineTrace method eps t) = _
  rw [affineTrace_take method eps (Nat.le_of_lt ht)]
  rfl

end V7.Stage6StrictDeterministic
