import PythagoreanSession.Order

/-!
# Dave's side: one square, cut in two ways

Dave's first cutting is Bob's figure, checked in `Bob.lean`. This file
checks his second cutting in coordinates, the angle at a corner of the
middle figure, and what he says happens at 60°.

The second cutting, with P at `(0, 0)`, the side PQ along `x` and the side
PS along `y`:

```
P---a---A------b------Q
|       |             |
a  a·a  |    a·b      |
|       |             |
E-------F-------------G
|       |             |
b  a·b  |    b·b      |
|       |             |
S-------H-------------R
```

Not checked here: his steps 5 to 7, 20 and 21, which are side-angle-side,
and the existence of the square, his step 3. The algebra of steps 24 and 25
is `dave_core` in `Cores.lean`.
-/

namespace PythagoreanSession.Dave

open Lean.Grind

set_option linter.unusedSectionVars false

variable {α : Type} [Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α] [OrderedRing α]

/-! ## Steps 2 and 9: the corner of the middle figure -/

/-- Step 9. `r` is a right angle. The two other angles of the triangle make
one right angle, and three angles along the straight line PAQ make two. So
the third angle at A is a right angle. -/
theorem step9_corner_is_right (r al be corner : α)
    (step2 : al + be = r) (straight : be + corner + al = 2 * r) : corner = r := by
  grind

/-- Dave's mended proof at 60°: the two other angles make 120°, and the
corner of the middle figure comes out as 60°, so it is not a square. -/
theorem corner_at_sixty_degrees (al be corner : Int)
    (step2 : al + be = 120) (straight : be + corner + al = 180) :
    corner = 60 ∧ corner ≠ 90 := by
  omega

/-! ## Steps 15 to 18: the second cutting -/

/-- The square PQRS. -/
def Square (a b x y : α) : Prop := 0 ≤ x ∧ x ≤ a + b ∧ 0 ≤ y ∧ y ≤ a + b
/-- PAFE, the square on `a`. -/
def PAFE (a x y : α) : Prop := 0 ≤ x ∧ x ≤ a ∧ 0 ≤ y ∧ y ≤ a
/-- AQGF, a rectangle `b` by `a`. -/
def AQGF (a b x y : α) : Prop := a ≤ x ∧ x ≤ a + b ∧ 0 ≤ y ∧ y ≤ a
/-- EFHS, a rectangle `a` by `b`. -/
def EFHS (a b x y : α) : Prop := 0 ≤ x ∧ x ≤ a ∧ a ≤ y ∧ y ≤ a + b
/-- FGRH, the square on `b`. -/
def FGRH (a b x y : α) : Prop := a ≤ x ∧ x ≤ a + b ∧ a ≤ y ∧ y ≤ a + b

/-- Step 17: the sides of the four rectangles. -/
theorem step17_sides (a b : α) :
    (a - 0 = a ∧ a - 0 = a) ∧ ((a + b) - a = b ∧ a - 0 = a) ∧
      (a - 0 = a ∧ (a + b) - a = b) ∧ ((a + b) - a = b ∧ (a + b) - a = b) := by
  grind

/-- Steps 15 and 16: the two lines cut the square into the four rectangles.
Every point of the square is in one of them, and each of them is in the
square. -/
theorem step16_four_rectangles (a b x y : α) (ha : 0 < a) (hb : 0 < b) :
    Square a b x y ↔ (PAFE a x y ∨ AQGF a b x y ∨ EFHS a b x y ∨ FGRH a b x y) := by
  simp only [Square, PAFE, AQGF, EFHS, FGRH]
  grind

/-- Two of the four rectangles share only points of the cuts `x = a` and
`y = a`. -/
theorem step16_rectangles_meet_on_cuts (a b x y : α) :
    (PAFE a x y → AQGF a b x y → x = a) ∧ (PAFE a x y → EFHS a b x y → y = a) ∧
    (PAFE a x y → FGRH a b x y → x = a ∧ y = a) ∧
    (AQGF a b x y → EFHS a b x y → x = a ∧ y = a) ∧
    (AQGF a b x y → FGRH a b x y → y = a) ∧ (EFHS a b x y → FGRH a b x y → x = a) := by
  simp only [PAFE, AQGF, EFHS, FGRH]
  grind

/-- The four rectangles have the areas `a²`, `ab`, `ab` and `b²`, and these
make up `(a + b)²`. -/
theorem second_cutting_adds_up (a b : α) :
    a * a + b * a + a * b + b * b = (a + b) ^ 2 := by
  grind

/-! ## Steps 19 and 21: a diagonal cuts a rectangle into two triangles

The diagonal from S `(0, a+b)` to F `(a, a)` is the line
`bx + ay = a(a + b)`. The diagonal from F `(a, a)` to Q `(a+b, 0)` is the
line `ax + by = a(a + b)`. -/

theorem step19_diagonals_pass_through_the_corners (a b : α) :
    (b * 0 + a * (a + b) = a * (a + b) ∧ b * a + a * a = a * (a + b)) ∧
      (a * a + b * a = a * (a + b) ∧ a * (a + b) + b * 0 = a * (a + b)) := by
  grind

/-- Every point of a rectangle is on one side of its diagonal or on the
other, and a point on both sides is on the diagonal. This is Dave's new
item 16, "a straight cut makes two pieces", for the two cuts he makes. -/
theorem step19_diagonal_makes_two_pieces (a b x y : α) :
    (EFHS a b x y →
      (b * x + a * y ≤ a * (a + b) ∨ a * (a + b) ≤ b * x + a * y)) ∧
    (b * x + a * y ≤ a * (a + b) → a * (a + b) ≤ b * x + a * y →
      b * x + a * y = a * (a + b)) ∧
    (AQGF a b x y →
      (a * x + b * y ≤ a * (a + b) ∨ a * (a + b) ≤ a * x + b * y)) ∧
    (a * x + b * y ≤ a * (a + b) → a * (a + b) ≤ a * x + b * y →
      a * x + b * y = a * (a + b)) := by
  simp only [EFHS, AQGF]
  grind

end PythagoreanSession.Dave
