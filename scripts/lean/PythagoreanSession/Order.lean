/-!
# Ordered fields: the few facts about order that the proofs need

The statements about positions on the grid are stated for an arbitrary
ordered field, so they hold for the real numbers. Core Lean decides
equations between polynomials and inequalities of the first degree by
itself. A product of two unknowns needs the lemmas below.
-/

namespace PythagoreanSession

open Lean.Grind

set_option linter.unusedSectionVars false

variable {α : Type} [Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α] [OrderedRing α]

theorem pos_mul {a b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  OrderedRing.mul_pos ha hb

theorem nonneg_mul {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  OrderedRing.mul_nonneg ha hb

/-- An inequality may be multiplied by a number that is not negative. -/
theorem mul_le {k x y : α} (hk : 0 ≤ k) (h : x ≤ y) : k * x ≤ k * y := by
  have h1 : 0 ≤ y - x := by grind
  have := nonneg_mul hk h1
  grind

/-- A positive factor may be cancelled from an inequality. -/
theorem le_of_mul_le {k x y : α} (hk : 0 < k) (h : k * x ≤ k * y) : x ≤ y := by
  refine Classical.byContradiction fun hn => ?_
  have h1 : 0 < x - y := by grind
  have := pos_mul hk h1
  grind

/-- `a² + b²` is positive when `a` and `b` are. -/
theorem sum_squares_pos {a b : α} (ha : 0 < a) (hb : 0 < b) : 0 < a * a + b * b := by
  have := pos_mul ha ha
  have := pos_mul hb hb
  grind

end PythagoreanSession
