/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Batteries.Linter.DeprecatedModule

/-
The linter ignores `Batteries.Linter.DeprecatedModule` so we need to add a
message here to indicate the proper replacement.
-/
deprecated_module "use Batteries.Linter.DeprecatedModule instead" (since := "2026-05-13")
