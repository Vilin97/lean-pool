/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Audits.Section8
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Audits.All

/-!
# Davis--Kahan diagnostic audits

This explicit target collects the print-heavy theorem-surface and dependency
audits. The ordinary `DavisKahan.All` build contains the mathematical library and
source-facing theorem surface without these diagnostic printouts.

Run `lake build DavisKahan.Audits.All` when the audit output is needed.
-/

@[expose] public section
