import Mathlib.Tactic.Hint
/--
info: Try these:
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example (h : 1 < 0) : False := by
  try?

/--
warning: The `hint` tactic is deprecated. Use `try?` instead.
---
info: Try these:
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example (h : 1 < 0) : False := by
  hint
