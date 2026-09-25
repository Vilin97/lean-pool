/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Basic

/-!
# Nonarchimedean Scottish Book — Problem 40

**Proposer:** Kiran Kedlaya
**Date:** 26 April 2022

## Problem Statement

Let (X_n → S) be an inverse system to an affinoid perfectoid space S. If each fiber admits
a tilde-inverse limit, does the original system admit a tilde-inverse limit?

## Notes

None.

## Status

Open.

## Definitions needed

- **Tilde-inverse limit**: The perfectoid space X ~ lim X_n such that |X| = lim |X_n| and
  O_X^+ is the p-adic completion of colim O_{X_n}^+; a universal object in the category
  of perfectoid spaces mapping to all X_n.
- **Affinoid perfectoid space**: An adic space of the form Spa(A, A+) where A is a
  perfectoid ring.
-/
