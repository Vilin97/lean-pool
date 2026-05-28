/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

import LeanPool.ErdosTuzaValtr.Config.Default

variable {α : Type _} [LinearOrder α] (C : Config α)

namespace Config

def HasLaced (n : ℕ) (S : Finset α) (p q : α) : Prop :=
  ∃ (a b : ℕ) (cp c cq : List α) (hcp : C.NCup a cp) (hc : C.NCup n c) (hcQ : C.NCup b cq),
    (cp.In S ∧ c.In S ∧ cq.In S) ∧
      a + b = n ∧ p ∈ cp.getLast? ∧ p ∈ c.head? ∧ q ∈ c.getLast? ∧ q ∈ cq.head?

theorem HasLaced.mem_ends {C : Config α} {n : ℕ} {S : Finset α} {p q : α} (h : C.HasLaced n S p q) :
    p ∈ S ∧ q ∈ S :=
  by
  rcases h with ⟨-, -, -, c, -, -, -, -, ⟨-, c_in_S, -⟩, -, ⟨-, c_head, c_last, -⟩⟩
  exact ⟨c_in_S _ (List.mem_of_mem_head? c_head), c_in_S _ (List.mem_of_mem_getLast? c_last)⟩

def HasInterweavedLaced (n : ℕ) (S : Finset α) (p q r s : α) : Prop :=
  (p < q ∧ q ≤ r ∧ r < s) ∧ C.HasLaced n S p r ∧ C.HasLaced n S q s

def HasJoin (a b : ℕ) (S : Finset α) : Prop :=
  ∃ (p : α) (cl cr : List α),
    (C.NCup a cl ∧ cl.In S ∧ p ∈ cl.getLast?) ∧ C.NCup b cr ∧ cr.In S ∧ p ∈ cr.head?

end Config
