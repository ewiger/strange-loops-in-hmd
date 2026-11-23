import PythagoreanSession.Order

/-!
# Carol's side: similar triangles, and what topology cannot say

Carol's proof has two parts. Steps 1 to 12 place the foot H of the
perpendicular between A and B, by arguments about order and angles. Steps
13 to 21 are ratios. The ratios are `carol_core` in `Cores.lean`. This file
checks the arithmetic of angles in steps 3, 4 and 8, the place of H in
coordinates, her remarks on scaling and shearing, and what she says happens
at 60°.

Not checked here: her steps 5 to 7 and 9 to 13 as she wrote them, from her
own list. They speak of points, rays and "between", and this project has
no formal geometry to state them in.
-/

namespace PythagoreanSession.Carol

open Lean.Grind

set_option linter.unusedSectionVars false

variable {α : Type} [Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α] [OrderedRing α]

/-! ## Topology cannot state the theorem -/

/-- A statement that cannot tell the triangle 3, 4, 5 from the triangle
3, 4, 6 is not the theorem. That bending turns one into the other is
Carol's premise and is not formalised. -/
theorem no_statement_from_topology (P : Nat → Nat → Nat → Prop)
    (blind : P 3 4 5 ↔ P 3 4 6) :
    ¬ ∀ a b c, P a b c ↔ a * a + b * b = c * c := by
  intro h
  have h5 := h 3 4 5
  have h6 := h 3 4 6
  simp at h5 h6
  exact h6 (blind.mp h5)

/-- The triangle 3, 4, 6 exists, and no choice of its long side satisfies
the equation. By the theorem itself, read backwards, it has no right
angle. The converse is not used. -/
theorem three_four_six :
    (3 + 4 > 6) ∧ (3 * 3 + 4 * 4 ≠ 6 * 6) ∧ (3 * 3 + 6 * 6 ≠ 4 * 4) ∧
      (4 * 4 + 6 * 6 ≠ 3 * 3) ∧ (3 * 3 + 4 * 4 = 5 * 5) := by
  decide

/-! ## Scaling and shearing -/

/-- Scaling by `k`: the equation is true of the scaled triangle exactly when
it was true before. -/
theorem scaling_keeps_the_theorem (a b c k : α) (hk : k ≠ 0) :
    (k * a) ^ 2 + (k * b) ^ 2 = (k * c) ^ 2 ↔ a ^ 2 + b ^ 2 = c ^ 2 := by
  constructor
  · intro h
    have h2 : k ^ 2 * (a ^ 2 + b ^ 2 - c ^ 2) = 0 := by grind
    grind
  · intro h
    grind

/-- A shear turns a right angle into one that is not right. The shear
`(x, y) ↦ (x + y, y)` leaves `(1, 0)` alone and sends `(0, 1)` to `(1, 1)`.
The first pair of arrows is perpendicular and the second is not. -/
theorem shear_breaks_the_right_angle :
    (1 : Int) * 0 + 0 * 1 = 0 ∧ (1 : Int) * (0 + 1) + 0 * 1 ≠ 0 := by
  decide

/-- Twice the area of the triangle with corners `p`, `q`, `r`, with a sign.
This is the area of the coordinate plane, taken as known. -/
def area2 (px py qx qy rx ry : α) : α :=
  (qx - px) * (ry - py) - (rx - px) * (qy - py)

/-- What Bob and Dave would not grant without proof: a shear keeps the area.
The shear is `(x, y) ↦ (x + s·y, y)`. -/
theorem shear_keeps_area (s px py qx qy rx ry : α) :
    area2 (px + s * py) py (qx + s * qy) qy (rx + s * ry) ry =
      area2 px py qx qy rx ry := by
  simp only [area2]
  grind

/-- What Bob and Dave would not grant without proof: scaling by `k`
multiplies the area by `k²`. -/
theorem scaling_multiplies_area_by_square (k px py qx qy rx ry : α) :
    area2 (k * px) (k * py) (k * qx) (k * qy) (k * rx) (k * ry) =
      k ^ 2 * area2 px py qx qy rx ry := by
  simp only [area2]
  grind

/-! ## Steps 3, 4 and 8: the arithmetic of angles

`r` is a right angle, so a straight angle is `2 * r`. -/

/-- Step 3. -/
theorem step3 (r al be ga : α) (sum : al + be + ga = 2 * r) (right : ga = r) :
    al + be = r := by
  grind

/-- Step 4: both other angles are acute. -/
theorem step4 (r al be : α) (step3 : al + be = r) (hal : 0 < al) (hbe : 0 < be) :
    al < r ∧ be < r := by
  grind

/-- Step 8. If A were between H and B, the triangle CHA would have a right
angle at H, the angle `2r − α` at A and something at C. That is more than
two right angles. -/
theorem step8_too_much_angle (r al atC : α) (acute : al < r) (hC : 0 < atC) :
    2 * r < r + (2 * r - al) + atC := by
  grind

/-! ## Step 10 in coordinates: the foot falls between A and B

Put C at `(0, 0)`, A at `(b, 0)` and B at `(0, a)`. The point at the
fraction `t` of the way from A to B is `(b(1 − t), at)`. The foot of the
perpendicular is the one with `t(a² + b²) = b²`. -/

theorem foot_is_between (a b t : α) (ha : 0 < a) (hb : 0 < b)
    (ht : t * (a * a + b * b) = b * b) :
    -- CH is perpendicular to AB
    (b * (1 - t)) * (0 - b) + (a * t) * (a - 0) = 0 ∧
    -- H is strictly between A and B
    0 < t ∧ t < 1 := by
  have hs := sum_squares_pos ha hb
  have haa := pos_mul ha ha
  have hbb := pos_mul hb hb
  refine ⟨by grind, ?_, ?_⟩
  · refine Classical.byContradiction fun hn => ?_
    have h1 : 0 ≤ -t := by grind
    have := nonneg_mul h1 (Std.le_of_lt hs)
    grind
  · refine Classical.byContradiction fun hn => ?_
    have h1 : 0 ≤ t - 1 := by grind
    have := nonneg_mul h1 (Std.le_of_lt hs)
    grind

/-! ## At 60° -/

/-- With 60° at C the small triangle has the angles `α`, 90, `90 − α` and
the large one `α`, 60, `120 − α`. For the two to have the same angles, the
right angle of the small one must appear in the large one. That happens
only when `α = 30`, and then `β = 90`: a different right triangle, as Carol
says. -/
theorem no_matching_at_sixty (al : Int) (h0 : 0 < al) (h1 : al < 90)
    (match_ : 90 = al ∨ 90 = 60 ∨ 90 = 120 - al) : al = 30 ∧ 120 - al = 90 := by
  omega

/-- The repaired cut. With one cut for each side, similar triangles still
give `b² = c·p` and `a² = c·q`. The theorem then holds exactly when the two
pieces make up the long side. The whole proof hangs on step 20. -/
theorem repaired_cut (a b c p q : α) (hc : c ≠ 0)
    (hb : b * b = c * p) (ha : a * a = c * q) :
    a * a + b * b = c * c ↔ p + q = c := by
  constructor
  · intro h
    have h2 : c * (p + q - c) = 0 := by grind
    grind
  · intro h
    grind

/-- The triangle with all sides 1 and all angles 60°: each cut lands on the
far corner, so each piece is the whole side. The pieces together are 2 and
the side is 1. -/
theorem repaired_cut_on_the_equal_sided_triangle :
    let a : Int := 1; let b : Int := 1; let c : Int := 1
    let p : Int := 1; let q : Int := 1
    b * b = c * p ∧ a * a = c * q ∧ p + q = 2 ∧ p + q ≠ c ∧
      a * a + b * b = c * 2 ∧ c * c = 1 := by
  decide

/-- "At a right angle, and only there, they meet exactly." With the angle
`γ` at C the third side satisfies `c² = a² + b² − 2ab·k`, where `k` is the
cosine of `γ`. That rule is taken as a hypothesis here. Then the two pieces
make up the long side exactly when `k = 0`. -/
theorem pieces_meet_only_at_a_right_angle (a b c p q k : α)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc : c ≠ 0)
    (hb : b * b = c * p) (ha : a * a = c * q)
    (cosine_rule : c * c = a * a + b * b - 2 * a * b * k) :
    p + q = c ↔ k = 0 := by
  have h2 : (2 : α) ≠ 0 := by grind
  constructor
  · intro h
    have : a * b * k = 0 := by grind
    grind
  · intro h
    have h3 : c * (p + q - c) = 0 := by grind
    grind

end PythagoreanSession.Carol
