import PythagoreanSession.Order

/-!
# Bob's side: the figure on the grid

Bob's steps 2, 3, 7, 8, 10, 13, 14, 15 and 16 are statements about
polynomials in two positive numbers `a` and `b`. Bob says a machine can
check them. This file does.

The points, as in his step 2:

```
O = (0, 0)      K = (a+b, 0)      L = (a+b, a+b)      M = (0, a+b)
P = (b, 0)      R = (a+b, b)      S = (a, a+b)        Q = (0, a)
```

Not checked here: his steps 4, 5, 6, 9 and 11, which use side-angle-side
and the angles of a triangle, and steps 18 to 21, which use area. The
algebra of step 22 is `bob_core` in `Cores.lean`.
-/

namespace PythagoreanSession.Bob

open Lean.Grind

set_option linter.unusedSectionVars false

variable {α : Type} [Field α] [LE α] [LT α] [Std.IsLinearOrder α]
  [Std.LawfulOrderLT α] [OrderedRing α]

/-! ## Step 2: eight different points -/

theorem step2_eight_different_points (a b : α) (ha : 0 < a) (hb : 0 < b) :
    List.Pairwise (· ≠ ·)
      [((0 : α), (0 : α)), (a + b, 0), (a + b, a + b), (0, a + b),
        (b, 0), (a + b, b), (a, a + b), (0, a)] := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, ne_eq, Prod.mk.injEq, List.Pairwise.nil,
    and_true]
  have h1 : a + b ≠ b := by grind
  have h2 : a + b ≠ a := by grind
  have h3 : a + b ≠ 0 := by grind
  have h4 : a ≠ 0 := by grind
  have h5 : b ≠ 0 := by grind
  grind

/-! ## Step 3: the legs of the four triangles, measured along the axes

Every length Bob reads from the grid is the difference of two coordinates
on a horizontal or a vertical line. -/

theorem step3_axis_lengths (a b : α) :
    -- T1: OP, OQ        T2: PK, KR
    b - 0 = b ∧ a - 0 = a ∧ (a + b) - b = a ∧ b - 0 = b ∧
    -- T3: RL, LS        T4: SM, MQ
    (a + b) - b = a ∧ (a + b) - a = b ∧ a - 0 = a ∧ (a + b) - a = b := by
  grind

/-! ## Step 7: the four lines -/

theorem step7_lines (a b : α) :
    -- the line through P and Q is `ax + by = ab`
    (a * b + b * 0 = a * b ∧ a * 0 + b * a = a * b) ∧
    -- the line through P and R is `bx − ay = b²`
    (b * b - a * 0 = b * b ∧ b * (a + b) - a * b = b * b) ∧
    -- the line through R and S is `ax + by = a² + ab + b²`
    (a * (a + b) + b * b = a * a + a * b + b * b ∧
      a * a + b * (a + b) = a * a + a * b + b * b) ∧
    -- the line through S and Q is `bx − ay = −a²`
    (b * a - a * (a + b) = -(a * a) ∧ b * 0 - a * a = -(a * a)) := by
  grind

/-! ## Steps 8 and 10: which side of a line a point is on -/

/-- At P: Q and R have `y > 0`; on the line PR, `bx − ay` is `−a²` at Q and
`0` at O, both less than `b²`. -/
theorem step8_at_P (a b : α) (ha : 0 < a) (hb : 0 < b) :
    (0 < b ∧ b < a + b) ∧ (0 < a ∧ 0 < b) ∧
      (b * 0 - a * a < b * b ∧ b * 0 - a * 0 < b * b) := by
  have := pos_mul ha ha
  have := pos_mul hb hb
  grind

/-- At R: P and S have `x < a + b`; on the line RS, `ax + by` is `ab` at P
and `a² + ab` at K, both less than `a² + ab + b²`. -/
theorem step10_at_R (a b : α) (ha : 0 < a) (hb : 0 < b) :
    (b < a + b ∧ a < a + b) ∧
      (a * b + b * 0 < a * a + a * b + b * b ∧
        a * (a + b) + b * 0 < a * a + a * b + b * b) := by
  have := pos_mul ha ha
  have := pos_mul hb hb
  grind

/-- At S: R and Q have `y < a + b`; on the line SQ, `bx − ay` is `b²` at R
and `b² − a²` at L, both more than `−a²`. -/
theorem step10_at_S (a b : α) (ha : 0 < a) (hb : 0 < b) :
    (b < a + b ∧ a < a + b) ∧
      (-(a * a) < b * (a + b) - a * b ∧
        -(a * a) < b * (a + b) - a * (a + b) ∧
        b * (a + b) - a * (a + b) = b * b - a * a) := by
  have := pos_mul ha ha
  have := pos_mul hb hb
  grind

/-- At Q: S and P have `x > 0`; on the line QP, `ax + by` is
`a² + ab + b²` at S and `ab + b²` at M, both more than `ab`. -/
theorem step10_at_Q (a b : α) (ha : 0 < a) (hb : 0 < b) :
    (0 < a ∧ 0 < b) ∧
      (a * b < a * a + b * (a + b) ∧ a * b < a * 0 + b * (a + b)) := by
  have := pos_mul ha ha
  have := pos_mul hb hb
  grind

/-! ## Step 13: the six figures as sets of points -/

/-- The large square W = OKLM. -/
def W (a b x y : α) : Prop := 0 ≤ x ∧ x ≤ a + b ∧ 0 ≤ y ∧ y ≤ a + b
/-- T1 = OPQ. -/
def T1 (a b x y : α) : Prop := 0 ≤ x ∧ 0 ≤ y ∧ a * x + b * y ≤ a * b
/-- T2 = PKR. -/
def T2 (a b x y : α) : Prop := 0 ≤ y ∧ x ≤ a + b ∧ b * b ≤ b * x - a * y
/-- T3 = RLS. -/
def T3 (a b x y : α) : Prop :=
  x ≤ a + b ∧ y ≤ a + b ∧ a * a + a * b + b * b ≤ a * x + b * y
/-- T4 = SMQ. -/
def T4 (a b x y : α) : Prop := y ≤ a + b ∧ 0 ≤ x ∧ b * x - a * y ≤ -(a * a)
/-- The middle figure PRSQ. -/
def Middle (a b x y : α) : Prop :=
  a * b ≤ a * x + b * y ∧ b * x - a * y ≤ b * b ∧
    a * x + b * y ≤ a * a + a * b + b * b ∧ -(a * a) ≤ b * x - a * y

/-- The inner side of each slanted line is the one that holds the corner not
on it: K for T2, L for T3, M for T4, and S and Q for the middle. -/
theorem step13_inner_sides (a b : α) (ha : 0 < a) (hb : 0 < b) :
    T1 a b 0 0 ∧ T2 a b (a + b) 0 ∧ T3 a b (a + b) (a + b) ∧ T4 a b 0 (a + b) ∧
      Middle a b a (a + b) ∧ Middle a b 0 a := by
  have := pos_mul ha ha
  have := pos_mul hb hb
  have := pos_mul ha hb
  simp only [T1, T2, T3, T4, Middle]
  grind

/-! ## Step 14: each piece lies in the large square -/

theorem step14_T1_bounds (a b x y : α) (ha : 0 < a) (hb : 0 < b) (h : T1 a b x y) :
    x ≤ b ∧ y ≤ a := by
  obtain ⟨hx, hy, h⟩ := h
  have := nonneg_mul (Std.le_of_lt ha) hx
  have := nonneg_mul (Std.le_of_lt hb) hy
  exact ⟨le_of_mul_le ha (by grind), le_of_mul_le hb (by grind)⟩

theorem step14_T2_bounds (a b x y : α) (ha : 0 < a) (hb : 0 < b) (h : T2 a b x y) :
    b ≤ x ∧ y ≤ b := by
  obtain ⟨hy, hx, h⟩ := h
  have := nonneg_mul (Std.le_of_lt ha) hy
  have := mul_le (Std.le_of_lt hb) hx
  exact ⟨le_of_mul_le hb (by grind), le_of_mul_le ha (by grind)⟩

theorem step14_T3_bounds (a b x y : α) (ha : 0 < a) (hb : 0 < b) (h : T3 a b x y) :
    a ≤ x ∧ b ≤ y := by
  obtain ⟨hx, hy, h⟩ := h
  have := mul_le (Std.le_of_lt ha) hx
  have := mul_le (Std.le_of_lt hb) hy
  exact ⟨le_of_mul_le ha (by grind), le_of_mul_le hb (by grind)⟩

theorem step14_T4_bounds (a b x y : α) (ha : 0 < a) (hb : 0 < b) (h : T4 a b x y) :
    x ≤ a ∧ a ≤ y := by
  obtain ⟨hy, hx, h⟩ := h
  have := nonneg_mul (Std.le_of_lt hb) hx
  have := mul_le (Std.le_of_lt ha) hy
  exact ⟨le_of_mul_le hb (by grind), le_of_mul_le ha (by grind)⟩

/-- The middle figure lies in W. This is Bob's four lines "multiply and add
the four inequalities in pairs", and the factor `a² + b²` turns up, as he
says, before any area does. -/
theorem step14_middle_in_W (a b x y : α) (ha : 0 < a) (hb : 0 < b)
    (h : Middle a b x y) : W a b x y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ha' := Std.le_of_lt ha
  have hb' := Std.le_of_lt hb
  have hs := sum_squares_pos ha hb
  have a1 := mul_le ha' h1
  have a2 := mul_le ha' h2
  have a3 := mul_le ha' h3
  have a4 := mul_le ha' h4
  have b1 := mul_le hb' h1
  have b2 := mul_le hb' h2
  have b3 := mul_le hb' h3
  have b4 := mul_le hb' h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_of_mul_le hs (by grind)
  · exact le_of_mul_le hs (by grind)
  · exact le_of_mul_le hs (by grind)
  · exact le_of_mul_le hs (by grind)

theorem step14_pieces_in_W (a b x y : α) (ha : 0 < a) (hb : 0 < b)
    (h : T1 a b x y ∨ T2 a b x y ∨ T3 a b x y ∨ T4 a b x y ∨ Middle a b x y) :
    W a b x y := by
  rcases h with h | h | h | h | h
  · have := step14_T1_bounds a b x y ha hb h
    simp only [T1, W] at *; grind
  · have := step14_T2_bounds a b x y ha hb h
    simp only [T2, W] at *; grind
  · have := step14_T3_bounds a b x y ha hb h
    simp only [T3, W] at *; grind
  · have := step14_T4_bounds a b x y ha hb h
    simp only [T4, W] at *; grind
  · exact step14_middle_in_W a b x y ha hb h

/-! ## Step 15: every point of the large square lies in a piece -/

theorem step15_W_is_covered (a b x y : α) (h : W a b x y) :
    T1 a b x y ∨ T2 a b x y ∨ T3 a b x y ∨ T4 a b x y ∨ Middle a b x y := by
  simp only [T1, T2, T3, T4, Middle, W] at *
  grind

/-! ## Step 16: two pieces share only points of an edge -/

theorem step16_triangle_and_middle (a b x y : α) :
    (T1 a b x y → Middle a b x y → a * x + b * y = a * b) ∧
    (T2 a b x y → Middle a b x y → b * x - a * y = b * b) ∧
    (T3 a b x y → Middle a b x y → a * x + b * y = a * a + a * b + b * b) ∧
    (T4 a b x y → Middle a b x y → b * x - a * y = -(a * a)) := by
  simp only [T1, T2, T3, T4, Middle]
  grind

private theorem cancel_R (a b x : α) (h : a * a + a * b + b * b ≤ a * x + b * b) :
    a * (a + b) ≤ a * x := by grind

private theorem cancel_S (a b y : α) (h : a * a + a * b + b * b ≤ a * a + b * y) :
    b * (a + b) ≤ b * y := by grind

private theorem cancel_Q (a b x : α) (h : a * x + b * a ≤ a * b) :
    a * x ≤ a * 0 := by grind

/-- T1 and T2 share the point P only. -/
theorem step16_T1_T2 (a b x y : α) (ha : 0 < a) (hb : 0 < b)
    (h1 : T1 a b x y) (h2 : T2 a b x y) : x = b ∧ y = 0 := by
  have b1 := step14_T1_bounds a b x y ha hb h1
  have b2 := step14_T2_bounds a b x y ha hb h2
  have hx : x = b := by grind
  obtain ⟨_, hy, h⟩ := h1
  have h0 : b * y ≤ b * 0 := by grind
  have := le_of_mul_le hb h0
  exact ⟨hx, by grind⟩

/-- T2 and T3 share the point R only. -/
theorem step16_T2_T3 (a b x y : α) (ha : 0 < a) (hb : 0 < b)
    (h2 : T2 a b x y) (h3 : T3 a b x y) : x = a + b ∧ y = b := by
  have b2 := step14_T2_bounds a b x y ha hb h2
  have b3 := step14_T3_bounds a b x y ha hb h3
  have hy : y = b := by grind
  obtain ⟨hx, _, h⟩ := h3
  rw [hy] at h
  have h0 : a * (a + b) ≤ a * x := cancel_R a b x h
  have := le_of_mul_le ha h0
  exact ⟨by grind, hy⟩

/-- T3 and T4 share the point S only. -/
theorem step16_T3_T4 (a b x y : α) (ha : 0 < a) (hb : 0 < b)
    (h3 : T3 a b x y) (h4 : T4 a b x y) : x = a ∧ y = a + b := by
  have b3 := step14_T3_bounds a b x y ha hb h3
  have b4 := step14_T4_bounds a b x y ha hb h4
  have hx : x = a := by grind
  obtain ⟨_, hy, h⟩ := h3
  rw [hx] at h
  have h0 : b * (a + b) ≤ b * y := cancel_S a b y h
  have := le_of_mul_le hb h0
  exact ⟨hx, by grind⟩

/-- T4 and T1 share the point Q only. -/
theorem step16_T4_T1 (a b x y : α) (ha : 0 < a) (hb : 0 < b)
    (h4 : T4 a b x y) (h1 : T1 a b x y) : x = 0 ∧ y = a := by
  have b4 := step14_T4_bounds a b x y ha hb h4
  have b1 := step14_T1_bounds a b x y ha hb h1
  have hy : y = a := by grind
  obtain ⟨hx, _, h⟩ := h1
  rw [hy] at h
  have h0 : a * x ≤ a * 0 := cancel_Q a b x h
  have := le_of_mul_le ha h0
  exact ⟨by grind, hy⟩

/-- T1 and T3 share nothing, and neither do T2 and T4. -/
theorem step16_opposite_triangles (a b x y : α) (ha : 0 < a) (hb : 0 < b) :
    ¬(T1 a b x y ∧ T3 a b x y) ∧ ¬(T2 a b x y ∧ T4 a b x y) := by
  have := sum_squares_pos ha hb
  simp only [T1, T2, T3, T4]
  grind

/-! ## A check from outside Bob's ground

Bob refuses the distance formula, and his proof gets "the middle is a
square" from side-angle-side. In the coordinate plane with the usual
length the same thing can be read off directly: the sides of PRSQ are the
arrows `(−b, a)`, `(a, b)`, `(−b, a)`, `(a, b)`, neighbours are at a right
angle, and every side has the squared length `a² + b²`. This is not part of
his proof. It shows that his figure is the right one. -/
theorem middle_is_a_square_in_the_usual_plane (a b : α) :
    -- PQ and PR are perpendicular
    (0 - b) * ((a + b) - b) + (a - 0) * (b - 0) = 0 ∧
    -- |PQ|² = |PR|² = |RS|² = |SQ|² = a² + b²
    (0 - b) ^ 2 + (a - 0) ^ 2 = a ^ 2 + b ^ 2 ∧
    ((a + b) - b) ^ 2 + (b - 0) ^ 2 = a ^ 2 + b ^ 2 ∧
    (a - (a + b)) ^ 2 + ((a + b) - b) ^ 2 = a ^ 2 + b ^ 2 ∧
    (0 - a) ^ 2 + (a - (a + b)) ^ 2 = a ^ 2 + b ^ 2 := by
  grind

end PythagoreanSession.Bob
