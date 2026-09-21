/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions

/-! # Potential Solenoidal -/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

/-- Gradients of `H¹` functions are public a.e.-based potential fields. -/
theorem potentialFieldOn_of_h1 {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    PotentialFieldOn U u.grad :=
  ⟨u.grad_memVectorL2, u, Filter.EventuallyEq.rfl⟩

/-- Gradients of `H¹₀` functions are public a.e.-based zero-trace potential
fields. -/
theorem potentialZeroTraceFieldOn_of_h10 {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) :
    PotentialZeroTraceFieldOn U u.toH1Function.grad :=
  ⟨u.toH1Function.grad_memVectorL2, u, Filter.EventuallyEq.rfl⟩

/-- Zero-trace potential fields are potential fields, at the public a.e.
surface. -/
theorem PotentialZeroTraceFieldOn.potentialFieldOn {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : PotentialZeroTraceFieldOn U f) :
    PotentialFieldOn U f := by
  rcases hf with ⟨hf_mem, u, hfg⟩
  exact ⟨hf_mem, u.toH1Function, hfg⟩

/-- Solenoidal fields with zero normal trace are solenoidal fields. -/
theorem SolenoidalZeroNormalTraceFieldOn.solenoidalFieldOn {d : ℕ}
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : SolenoidalZeroNormalTraceFieldOn U g) :
    SolenoidalFieldOn U g := by
  refine ⟨hg.1, ?_⟩
  intro φ
  exact hg.2 φ.toH1Function

end

end Ch01
end Book
end Homogenization
