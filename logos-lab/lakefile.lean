-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
import Lake
open Lake DSL

-- Exact pins. Lean core only: no external dependencies.
-- lean-toolchain pins leanprover/lean4:v4.12.0.
-- No Batteries / Std4 / Mathlib requirement is declared, deliberately:
-- Lean 4.12 core has no Finite, Fintype, or Rat, and this project
-- defines its own finiteness enumeration (see MEASURES.md §5) rather
-- than depending on a library that is not pinned and fetched here.
-- If a future phase adds a dependency, it must be pinned here with an
-- exact version / commit, and MEASURES.md updated first.
package logosLab where
  version := v!"0.1.0"

-- Library root is LogosLab.lean, which imports every submodule in
-- dependency order (Syntax, State, Measures, Guards, Finite, Examples).
lean_lib LogosLab where
  roots := #[`LogosLab]

@[default_target]
lean_exe logosLab where
  root := `Root
