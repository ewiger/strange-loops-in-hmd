/-!
# The three sides: the algebra each proof ends on

The Pythagoras classroom, discussion SLH-D-0005, holds three proofs that in a
right triangle `a² + b² = c²`. Each proof has a geometric part, which puts a
figure together, and an algebraic part, which turns the figure into the
equation. This file checks the algebraic part of each.

Everything is stated for an arbitrary field, so it holds for the real
numbers. Core Lean has no real numbers of its own, and this project uses
no library beyond core Lean.

What is *not* checked here: that the figures are what the provers say they
are. Bob's figure is checked in `Bob.lean`, in coordinates. Dave's and
Carol's rest on side-angle-side and on similar triangles, which are taken
as hypotheses below.
-/

namespace PythagoreanSession

open Lean.Grind

variable {α : Type} [Field α]

/-! ## The plain proof and Bob -/

/-- The six lines of the report, and Bob's steps 21 and 22. A square of side
`a + b` is four right triangles of area `ab / 2` and a square of side `c`. -/
theorem bob_core (a b c : α) (h : (a + b) ^ 2 = 4 * (a * b / 2) + c ^ 2) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  grind

/-! ## Dave -/

/-- Dave's steps 24 and 25. The same square is cut in two ways, and each
cutting has four copies of the triangle. `t` is the area of the triangle,
and nothing is assumed about it: Dave never needs the area of a triangle. -/
theorem dave_core (a b c t : α)
    (first : (a + b) ^ 2 = 4 * t + c ^ 2)
    (second : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 4 * t) :
    c ^ 2 = a ^ 2 + b ^ 2 := by
  grind

/-- Dave's offer in Act 1: "I can state the theorem about the areas of the
three squares and not need" the rule that a square of side `s` has the area
`s²`. Here `sa`, `sb`, `sc` are the areas of the three squares and `w` the
area of the large one, all unknown numbers. -/
theorem dave_core_squares_as_figures (w sa sb sc t : α)
    (first : w = 4 * t + sc) (second : w = sa + sb + 4 * t) :
    sc = sa + sb := by
  grind

/-! ## Carol -/

/-- Carol's steps 14 to 21. The foot of the perpendicular cuts the long side
into `p = AH` and `q = BH`. Similar triangles give the two ratios, and the
two pieces make up the long side. No area is used. -/
theorem carol_core (a b c p q : α) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ratio_b : p / b = b / c) (ratio_a : q / a = a / c) (pieces : p + q = c) :
    a * a + b * b = c * c := by
  grind

/-- Carol's steps 15 and 19 alone: each leg squared is the long side times
the piece next to it. -/
theorem carol_legs (a b c p q : α) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ratio_b : p / b = b / c) (ratio_a : q / a = a / c) :
    b * b = c * p ∧ a * a = c * q := by
  grind

/-! ## One proof or two? -/

/-- Bob's count and Dave's first cutting are the same equation once the
triangle is given the area `ab / 2`. So Bob's proof is Dave's first cutting
with one more fact, and Dave's second cutting replaces that fact. -/
theorem bob_is_dave_first_cutting (a b c : α) :
    ((a + b) ^ 2 = 4 * (a * b / 2) + c ^ 2) ↔
      ((a + b) ^ 2 = 4 * (a * b / 2) + c ^ 2 ∧
        (a + b) ^ 2 = a ^ 2 + b ^ 2 + 4 * (a * b / 2)) := by
  grind

/-- Carol's two products add up to the same square that Bob and Dave count,
so all three end on one identity. -/
theorem all_three_meet (a b c p q : α)
    (hb : b * b = c * p) (ha : a * a = c * q) (pieces : p + q = c) :
    (a + b) ^ 2 = 4 * (a * b / 2) + c ^ 2 := by
  grind

end PythagoreanSession
