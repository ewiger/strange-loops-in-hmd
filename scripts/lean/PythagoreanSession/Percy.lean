import PythagoreanSession.Order

/-!
# Percy's side: the places where the theorem might fail

Percy proves nothing. He names places where the formula fails and facts
that fail there. This file checks his examples.

The town is checked in full, with rational coordinates: it is the plane
with the length `|Δx| + |Δy|`. The ball is checked only as arithmetic.
This project has no spherical geometry, so "the polar triangle has three
right angles and three equal sides" is checked on the three arrows from
the centre, and the lengths of arcs are not formalised.
-/

namespace PythagoreanSession.Percy

open Lean.Grind

/-! ## The town of square blocks -/

/-- The size of a number, without its sign. -/
def size (x : Rat) : Rat := if 0 ≤ x then x else -x

/-- The length of the town: the streets walked. -/
def streets (px py qx qy : Rat) : Rat := size (qx - px) + size (qy - py)

/-- Two arrows are at a right angle. The town keeps the angles of the
plane. -/
def perpendicular (ux uy vx vy : Rat) : Prop := ux * vx + uy * vy = 0

/-- The street triangle: the corner at `(0, 0)`, legs to `(3, 0)` and
`(0, 4)`. Legs 3 and 4, third side 7, and `9 + 16` is not `49`. -/
theorem street_triangle :
    perpendicular 3 0 0 4 ∧ streets 0 0 3 0 = 3 ∧ streets 0 0 0 4 = 4 ∧
      streets 3 0 0 4 = 7 ∧ (3 : Rat) * 3 + 4 * 4 ≠ 7 * 7 := by
  simp only [perpendicular, streets, size]
  grind

/-- The turned triangle: the corner at `(0, 0)`, legs to `(1.5, 1.5)` and
`(−2, 2)`. Legs 3 and 4 at a right angle, third side 4. -/
theorem turned_triangle :
    perpendicular (3 / 2) (3 / 2) (-2) 2 ∧ streets 0 0 (3 / 2) (3 / 2) = 3 ∧
      streets 0 0 (-2) 2 = 4 ∧ streets (3 / 2) (3 / 2) (-2) 2 = 4 := by
  simp only [perpendicular, streets, size]
  grind

/-- G19, side-angle-side, is false in the town: two triangles with legs 3
and 4 at a right angle, and third sides 7 and 4. -/
theorem side_angle_side_fails_in_town :
    ¬ ∀ ax ay bx by' ax' ay' bx' by'' : Rat,
      perpendicular ax ay bx by' → perpendicular ax' ay' bx' by'' →
      streets 0 0 ax ay = streets 0 0 ax' ay' →
      streets 0 0 bx by' = streets 0 0 bx' by'' →
      streets ax ay bx by' = streets ax' ay' bx' by'' := by
  intro h
  have := h 3 0 0 4 (3 / 2) (3 / 2) (-2) 2
  simp only [perpendicular, streets, size] at this
  grind

/-- Every fact about Bob's grid holds in the town: along a street the
length is the difference of the coordinates (G26). So the grid does not
say which length is meant. -/
theorem grid_lengths_hold_in_town (x₁ x₂ y₁ y₂ : Rat) :
    streets x₁ y₁ x₂ y₁ = size (x₂ - x₁) ∧ streets x₁ y₁ x₁ y₂ = size (y₂ - y₁) := by
  simp only [streets, size]
  grind

/-- G16, lengths add along a line, holds in the town on every line, slanted
or not: for a point at the fraction `t` between two others. -/
theorem lengths_add_in_town (px py qx qy t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    streets px py (px + t * (qx - px)) (py + t * (qy - py)) +
      streets (px + t * (qx - px)) (py + t * (qy - py)) qx qy =
    streets px py qx qy := by
  have key : ∀ d : Rat, size (t * d) + size (d - t * d) = size d := by
    intro d
    have e1 : size (t * d) = t * size d := by
      simp only [size]
      rcases Rat.le_total (a := 0) (b := d) with hd | hd
      · have := Rat.mul_nonneg h0 hd
        grind
      · have : 0 ≤ t * (-d) := Rat.mul_nonneg h0 (by grind)
        grind
    have e2 : size (d - t * d) = (1 - t) * size d := by
      simp only [size]
      rcases Rat.le_total (a := 0) (b := d) with hd | hd
      · have : 0 ≤ (1 - t) * d := Rat.mul_nonneg (by grind) hd
        grind
      · have : 0 ≤ (1 - t) * (-d) := Rat.mul_nonneg (by grind) (by grind)
        grind
    grind
  have kx := key (qx - px)
  have ky := key (qy - py)
  simp only [streets]
  have ex : px + t * (qx - px) - px = t * (qx - px) := by grind
  have ey : py + t * (qy - py) - py = t * (qy - py) := by grind
  have fx : qx - (px + t * (qx - px)) = (qx - px) - t * (qx - px) := by grind
  have fy : qy - (py + t * (qy - py)) = (qy - py) - t * (qy - py) := by grind
  rw [ex, ey, fx, fy]
  grind

/-- G23 is false in the town. Measured the ordinary way, the turned
triangle has the squared sides 4.5, 8 and 12.5, which are 9, 16 and 25
halved: it has the shape of the triangle 3, 4, 5. Their town sides are
3, 4, 7 and 3, 4, 4, and those have no one ratio. -/
theorem same_shape_different_ratios :
    ((3 / 2 : Rat) ^ 2 + (3 / 2) ^ 2 = 9 / 2 ∧ ((-2 : Rat)) ^ 2 + 2 ^ 2 = 16 / 2 ∧
      ((-2 : Rat) - 3 / 2) ^ 2 + (2 - 3 / 2) ^ 2 = 25 / 2) ∧
    ((3 : Rat) / 3 = 4 / 4 ∧ (7 : Rat) / 4 ≠ 3 / 3) := by
  grind

/-- G21 is false in the town: turn the leg of 3 by half a right angle and
it runs to `(3s/2, 3s/2)`, where `s` is the square root of 2. Its town
length is `3s`, which is not 3. -/
theorem turning_changes_length (s : Rat) (hs : s * s = 2) (pos : 0 < s) :
    streets 0 0 (3 * s / 2) (3 * s / 2) = 3 * s ∧ 3 * s ≠ 3 := by
  simp only [streets, size]
  grind

/-- G33, G35 and G36 are false in the town. The square with the corners
`(½, 0)`, `(0, ½)`, `(−½, 0)`, `(0, −½)` has four right angles and four
sides of town length 1, like the square along the streets, and half its
area. -/
theorem turned_square_has_half_the_area :
    -- four sides of town length 1
    (streets (1 / 2) 0 0 (1 / 2) = 1 ∧ streets 0 (1 / 2) (-1 / 2) 0 = 1 ∧
      streets (-1 / 2) 0 0 (-1 / 2) = 1 ∧ streets 0 (-1 / 2) (1 / 2) 0 = 1) ∧
    -- neighbouring sides at a right angle
    (perpendicular (-1 / 2) (1 / 2) (-1 / 2) (-1 / 2) ∧
      perpendicular (-1 / 2) (-1 / 2) (1 / 2) (-1 / 2)) ∧
    -- its area, as two triangles on the diagonal of length 1, is one half
    ((1 : Rat) * (1 / 2) / 2 + 1 * (1 / 2) / 2 = 1 / 2 ∧ (1 / 2 : Rat) ≠ 1 * 1) := by
  simp only [perpendicular, streets, size]
  grind

/-- G37 is false in the town: the turned triangle has legs 3 and 4, so the
rule gives 6. Its area is 3. -/
theorem turned_triangle_area :
    ((3 / 2 : Rat) * 2 - (-2) * (3 / 2)) / 2 = 3 ∧ (3 : Rat) * 4 / 2 = 6 ∧
      (3 : Rat) ≠ 6 := by
  grind

/-! ## The ball -/

/-- The polar triangle, as arithmetic: three equal sides `L`. -/
theorem polar_triangle {α : Type} [Field α] (L : α) (hL : L ≠ 0) :
    L * L + L * L ≠ L * L := by
  grind

/-- The corners of the polar triangle are the ends of three arrows from the
centre of the ball, each at a right angle to the other two. From this come
its three right angles and its three equal sides. That step is geometry on
the ball and is not formalised. -/
theorem polar_triangle_arrows :
    let n : Int × Int × Int := (0, 0, 1)
    let e : Int × Int × Int := (1, 0, 0)
    let f : Int × Int × Int := (0, 1, 0)
    n.1 * e.1 + n.2.1 * e.2.1 + n.2.2 * e.2.2 = 0 ∧
    n.1 * f.1 + n.2.1 * f.2.1 + n.2.2 * f.2.2 = 0 ∧
    e.1 * f.1 + e.2.1 * f.2.1 + e.2.2 * f.2.2 = 0 := by
  decide

/-- G37 on the ball. With `p` for π and the radius 1: the rule gives
`p²/8`, about 1.23, and the eighth of the ball is `p/2`, about 1.57. -/
theorem triangle_area_rule_fails_on_ball (p : Rat) (lo : 314 / 100 < p)
    (hi : p < 315 / 100) :
    123 / 100 < p * p / 8 ∧ p * p / 8 < 125 / 100 ∧ 157 / 100 < p / 2 ∧
      p / 2 < 158 / 100 ∧ p * p / 8 ≠ p / 2 := by
  have h1 : 0 < (p - 314 / 100) * (p - 314 / 100) := Rat.mul_pos (by grind) (by grind)
  have h2 : 0 < (315 / 100 - p) * (p - 314 / 100) := Rat.mul_pos (by grind) (by grind)
  grind

/-! ## A world without √2 -/

/-- No fraction has the square 2. So if lengths must be fractions, the
triangle with legs 1 and 1 has no third side. -/
theorem no_fraction_has_square_two : ∀ q p : Nat, 0 < q → p * p ≠ 2 * (q * q) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro p hq h
    have even_of_sq : ∀ n m : Nat, n * n = 2 * m → n % 2 = 0 := by
      intro n m hn
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · exact h0
      · have := Nat.mul_mod n n 2
        rw [h1, hn] at this
        omega
    have hp := even_of_sq p (q * q) h
    obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k := ⟨p / 2, by omega⟩
    have h2 : q * q = 2 * (k * k) := by grind
    have hq2 := even_of_sq q (k * k) h2
    obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m := ⟨q / 2, by omega⟩
    have h3 : k * k = 2 * (m * m) := by grind
    exact ih m (by omega) k (by omega) h3

/-! ## A triangle with no width -/

/-- If `a = 0` the points B and C are one point, and the formula says only
that the two remaining sides are equal. It survives. -/
theorem no_width {α : Type} [Field α] (b c : α) (h : c = b) :
    (0 : α) * 0 + b * b = c * c := by
  grind

/-! ## What a drawing does not show -/

/-- Four equal sides make a rhombus, not a square. The figure with the
corners `(0,0)`, `(2,1)`, `(3,3)`, `(1,2)` has four sides of squared length
5, and its sides at `(0,0)` are not at a right angle. -/
theorem four_equal_sides_are_not_a_square :
    ((2 : Int) ^ 2 + 1 ^ 2 = 5 ∧ (1 : Int) ^ 2 + 2 ^ 2 = 5 ∧
      ((3 : Int) - 2) ^ 2 + (3 - 1) ^ 2 = 5 ∧ ((3 : Int) - 1) ^ 2 + (3 - 2) ^ 2 = 5) ∧
    (2 : Int) * 1 + 1 * 2 ≠ 0 := by
  decide

/-- The puzzle of 64 and 65. The square of 8 by 8 and the rectangle of 5 by
13 differ by one unit. The four pieces do not fit: the "diagonal" of the
rectangle passes `(5, 2)` and `(8, 3)`, which are not on the line from
`(0, 0)` to `(13, 5)`, and the gap between them is a thin figure of area
exactly 1. -/
theorem sixty_four_is_not_sixty_five :
    (8 * 8 = 64 ∧ 5 * 13 = 65 ∧ 64 ≠ 65) ∧
    -- (5, 2) and (8, 3) are off the diagonal, on opposite sides
    ((5 : Int) * 5 - 13 * 2 = -1 ∧ (5 : Int) * 8 - 13 * 3 = 1) ∧
    -- the area of the gap (0,0), (5,2), (13,5), (8,3), by its corners
    ((5 : Int) * 5 - 13 * 2 + (13 * 3 - 8 * 5)) / 2 * (-1) = 1 := by
  decide

end PythagoreanSession.Percy
