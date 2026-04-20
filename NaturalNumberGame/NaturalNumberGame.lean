import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic

namespace NNG

/-!
# Natural Number Game
-/

-- -------------------------------------------------------
-- Tutorial World
-- -------------------------------------------------------

-- Proposition 1.1

theorem prop_1_1 (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]  -- rewrite y as x + 7; goal becomes 2 * (x + 7) = 2 * (x + 7)
          -- closed by rfl automatically

theorem prop_1_1_alt (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [← h]  -- rewrite (x + 7) as y; goal becomes 2 * y = 2 * y
          -- closed by rfl automatically

-- Proposition 1.2

-- defining 1 and 2 in terms of succ
theorem one_eq_succ_zero : 1 = Nat.succ 0 := rfl
theorem two_eq_succ_one : 2 = Nat.succ 1 := rfl

-- Note: `rw` attempts to close the goal automatically
-- `rewrite` however, does not

theorem prop_1_2 : 2 = Nat.succ (Nat.succ 0) := by
  rw [two_eq_succ_one] -- rewrite 2 as succ 1; goal becomes succ 1 = succ (succ 0)
  -- closed by rw's automatic rfl (since 1 is definitionally Nat.succ 0)

theorem prop_1_2_alt : 2 = Nat.succ (Nat.succ 0) := by
  rewrite [two_eq_succ_one] -- rewrite 2 as succ 1; goal becomes succ 1 = succ (succ 0)
  rewrite [one_eq_succ_zero] -- rewrite 1 as succ 0; goal becomes succ (succ 0) = succ (succ 0)
  rfl -- closed by rfl

theorem prop_1_2_alt2 : 2 = Nat.succ (Nat.succ 0) := by
  rw [← one_eq_succ_zero] -- rewrite succ 0 as 1; goal becomes 2 = succ 1
  -- closed by rw's automatic rfl (since 2 is definitionally succ 1)

theorem prop_1_2_alt3 : 2 = Nat.succ (Nat.succ 0) := by
  rewrite [← one_eq_succ_zero] -- rewrite succ 0 as 1; goal becomes 2 = succ 1
  rewrite [← two_eq_succ_one] -- rewrite succ 1 as 2; goal becomes 2 = 2
  rfl -- closed by rfl

-- Proposition 1.3

theorem prop_1_3 (a b c : ℕ) : a + (b+0) + (c+0) = a + b + c := by
  rw [Nat.add_zero] -- rewrite b+0 as b; goal becomes a + b + (c+0) = a + b + c
  rw [Nat.add_zero] -- rewrite c+0 as c; goal becomes a + b + c = a + b + c

theorem prop_1_4 (n : ℕ) : Nat.succ n = n + 1 := by
  rfl -- closed by rfl automatically since `n + 1` and `Nat.succ n` are definitionally equal

theorem prop_1_4alt (n : ℕ) : Nat.succ n = n + 1 := by
  rewrite [one_eq_succ_zero] -- rewrite 1 as succ 0; goal becomes n.succ = n + succ 0
  rewrite [Nat.add_succ] -- rewrite n + succ 0 as (n + 0).succ; goal becomes n.succ = (n + 0).succ
  rewrite [Nat.add_zero] -- rewrite n + 0 as n; goal becomes n.succ = n.succ
  rfl -- closed by rfl



end NNG
