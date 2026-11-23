import PythagoreanSession.Order
import PythagoreanSession.Percy

/-!
# The disagreements between the sides

Each part below takes one dispute of the classroom and says, as a theorem,
what a machine can say about it. The disputes about the examples
themselves, the town, the ball and the triangle at 60°, are in `Percy.lean`,
`Carol.lean` and `Dave.lean`.
-/

namespace PythagoreanSession.Disagreements

open Lean.Grind

set_option linter.unusedSectionVars false

/-! ## The distance formula is the theorem in other clothes

All three provers refuse the distance formula to the textbook coordinate
proof. They are right, and the reason is a loop: the formula gives the
theorem in one line, and the theorem gives the formula in one line. -/

section DistanceFormula

variable {α : Type} [Field α]

/-- The distance formula, for a length `d` between the points `(x₁, y₁)`
and `(x₂, y₂)`. -/
def DistanceFormula (d : α → α → α → α → α) : Prop :=
  ∀ x₁ y₁ x₂ y₂, d x₁ y₁ x₂ y₂ ^ 2 = (x₂ - x₁) ^ 2 + (y₂ - y₁) ^ 2

/-- The theorem for every right triangle whose legs lie along the grid: the
corner at `(x, y)`, one leg of signed length `b` along `x`, the other of
signed length `a` along `y`. -/
def TheoremOnTheGrid (d : α → α → α → α → α) : Prop :=
  ∀ x y a b, a ^ 2 + b ^ 2 = d (x + b) y x (y + a) ^ 2

theorem formula_gives_theorem (d : α → α → α → α → α) (h : DistanceFormula d) :
    TheoremOnTheGrid d := by
  intro x y a b
  have := h (x + b) y x (y + a)
  grind

theorem theorem_gives_formula (d : α → α → α → α → α) (h : TheoremOnTheGrid d) :
    DistanceFormula d := by
  intro x₁ y₁ x₂ y₂
  have := h x₂ y₁ (y₂ - y₁) (x₁ - x₂)
  have e1 : x₂ + (x₁ - x₂) = x₁ := by grind
  have e2 : y₁ + (y₂ - y₁) = y₂ := by grind
  rw [e1, e2] at this
  grind

/-- The loop, closed. A proof of the theorem that starts from the distance
formula assumes what it proves. -/
theorem distance_formula_is_the_theorem (d : α → α → α → α → α) :
    DistanceFormula d ↔ TheoremOnTheGrid d :=
  ⟨formula_gives_theorem d, theorem_gives_formula d⟩

/-- Bob's second refusal: `sin² + cos² = 1` is the theorem for a long side
of length one. Here the sine is `a / c` and the cosine `b / c`. -/
theorem sine_and_cosine_are_the_theorem (a b c : α) (hc : c ≠ 0) :
    (a / c) ^ 2 + (b / c) ^ 2 = 1 ↔ a ^ 2 + b ^ 2 = c ^ 2 := by
  constructor
  · intro h
    have h2 : c ^ 2 * ((a / c) ^ 2 + (b / c) ^ 2) = c ^ 2 := by grind
    grind
  · intro h
    grind

end DistanceFormula

/-! ## Percy against Alice: the grid does not fix the length

Alice wrote that Bob's grid helps to fix which length is meant. Percy
answered that every fact about the grid is true in the town. Percy stands,
and Alice has said so. -/

/-- There is a length that agrees with Bob's grid along every horizontal
and vertical line and for which the theorem is false. -/
theorem grid_does_not_fix_the_length :
    ∃ len : Rat → Rat → Rat → Rat → Rat,
      (∀ x₁ x₂ y, len x₁ y x₂ y = Percy.size (x₂ - x₁)) ∧
      (∀ x y₁ y₂, len x y₁ x y₂ = Percy.size (y₂ - y₁)) ∧
      len 0 0 3 0 ^ 2 + len 0 0 0 4 ^ 2 ≠ len 3 0 0 4 ^ 2 := by
  refine ⟨Percy.streets, ?_, ?_, ?_⟩
  · intro x₁ x₂ y
    exact (Percy.grid_lengths_hold_in_town x₁ x₂ y y).1
  · intro x y₁ y₂
    exact (Percy.grid_lengths_hold_in_town x x y₁ y₂).2
  · simp only [Percy.streets, Percy.size]
    grind

/-! ## Percy against Dave: the area of a square

Dave calls "a square of side `s` has the area `s²`" a known result. Percy
answers that it cannot be proved from Dave's three rules of area, because
the rules stay true when every area is doubled. -/

section Area

variable {α : Type} [Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α] [OrderedRing α]

variable {Figure : Type}

/-- Dave's items 11, 12 and 13: every figure has an area that is not
negative, congruent figures have equal areas, and the areas of pieces add.
A cutting into more pieces is a cutting in two, done again. -/
def AreaRules (congruent : Figure → Figure → Prop)
    (cut : Figure → Figure → Figure → Prop) (area : Figure → α) : Prop :=
  (∀ f, 0 ≤ area f) ∧ (∀ f g, congruent f g → area f = area g) ∧
    (∀ f g h, cut f g h → area f = area g + area h)

/-- Doubling every area keeps the three rules. -/
theorem doubling_keeps_the_rules (congruent : Figure → Figure → Prop)
    (cut : Figure → Figure → Figure → Prop) (area : Figure → α)
    (h : AreaRules congruent cut area) :
    AreaRules congruent cut (fun f => 2 * area f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro f
    have := h1 f
    grind
  · intro f g hc
    have := h2 f g hc
    grind
  · intro f g k hc
    have := h3 f g k hc
    grind

/-- So the three rules cannot prove that a square of side `s` has the area
`s²`. Whenever an area obeys the rules and gives every square its `s²`,
another area obeys the same rules and does not. -/
theorem square_rule_is_not_forced (congruent : Figure → Figure → Prop)
    (cut : Figure → Figure → Figure → Prop) (area : Figure → α)
    (isSquare : Figure → Prop) (side : Figure → α)
    (rules : AreaRules congruent cut area)
    (squares : ∀ f, isSquare f → area f = side f * side f)
    (u : Figure) (hu : isSquare u) (hside : side u ≠ 0) :
    ∃ area' : Figure → α, AreaRules congruent cut area' ∧
      ¬ ∀ f, isSquare f → area' f = side f * side f := by
  refine ⟨fun f => 2 * area f, doubling_keeps_the_rules congruent cut area rules, ?_⟩
  intro h
  have h1 := h u hu
  have h2 := squares u hu
  have h3 : side u * side u = 0 := by grind
  grind

/-! ## Bob and the rule he says he does not use

Bob takes "a right triangle with legs `p` and `q` has the area `pq / 2`" as
a known result, and notes that no step of his uses "congruent polygons have
equal areas". Percy marks the first as resting on the second. Both are
right: Bob's steps do not cite the rule, and his known result cannot be had
without it. -/

/-- With the rule: a rectangle `p` by `q` cut by its diagonal into two
congruent triangles gives each the area `pq / 2`. -/
theorem triangle_area_from_rectangle (rectangle t₁ t₂ p q : α)
    (rule_rectangle : rectangle = p * q) (pieces_add : rectangle = t₁ + t₂)
    (congruent_equal : t₁ = t₂) : t₁ = p * q / 2 := by
  grind

/-- Without the rule: the rectangle rule and the adding of pieces allow the
two halves any areas that add up, for instance everything and nothing. -/
theorem triangle_area_needs_congruence (p q : α) (h : p * q ≠ 0) :
    ∃ rectangle t₁ t₂ : α, 0 ≤ t₂ ∧ rectangle = p * q ∧ rectangle = t₁ + t₂ ∧
      t₁ ≠ p * q / 2 := by
  refine ⟨p * q, p * q, 0, Std.le_refl 0, rfl, by grind, ?_⟩
  intro h1
  grind

end Area

/-! ## Without the right angle -/

/-- The triangle with all sides 1 and all angles 60°: the formula fails, so
every proof has to stop somewhere. Where each one stops is in `Dave.lean`
and `Carol.lean`. -/
theorem equal_sided_triangle : 1 * 1 + 1 * 1 = 2 ∧ 1 * 1 = 1 ∧ 2 ≠ 1 := by
  decide

/-! ## Side-angle-side: axiom or known result?

Whether a fact is an axiom or a known result is a choice of where to start,
and nothing here decides it. One thing can be decided: side-angle-side is
not a known result *of Bob's grid*. The town has the grid (G24 to G26), and
lengths add along every line there (G16), and side-angle-side is false in
it. So on a ground that holds the grid, it has to come in from outside. -/
theorem side_angle_side_is_not_a_result_of_the_grid :
    (∀ x₁ x₂ y₁ y₂ : Rat,
      Percy.streets x₁ y₁ x₂ y₁ = Percy.size (x₂ - x₁) ∧
        Percy.streets x₁ y₁ x₁ y₂ = Percy.size (y₂ - y₁)) ∧
    (Percy.streets 0 0 3 0 = Percy.streets 0 0 (3 / 2) (3 / 2) ∧
      Percy.streets 0 0 0 4 = Percy.streets 0 0 (-2) 2 ∧
      Percy.streets 3 0 0 4 ≠ Percy.streets (3 / 2) (3 / 2) (-2) 2) := by
  refine ⟨Percy.grid_lengths_hold_in_town, ?_⟩
  simp only [Percy.streets, Percy.size]
  grind

end PythagoreanSession.Disagreements
