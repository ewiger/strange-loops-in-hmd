/-!
# From distance to logic

The proofs behind `methodology/distance-to-logic.hmd`.

A distance that may differ in its two directions is read as a logic:
`a` entails `b` when the distance from `a` to `b` is zero. This file proves
that the reading is sound: the entailment is a preorder, a chain of asserted
steps bounds the distance it spans, and an ordinary preorder is the special
case where a distance takes only two values.

It also proves the two negative results the method rests on: a symmetric
distance cannot tell entailment from equivalence, and a signed distance makes
every two things comparable.

The file uses core Lean only. Check it with `lake build` in this folder.
-/

namespace DistanceLogic

/-! ## Costs -/

/-- What a distance is measured in. Costs are ordered and can be added, zero
is the least cost, and adding is monotone. The natural numbers are one
instance and the two truth values another. -/
class Cost (V : Type) extends LE V, Add V, Zero V where
  le_refl : ∀ a : V, a ≤ a
  le_trans : ∀ {a b c : V}, a ≤ b → b ≤ c → a ≤ c
  le_antisymm : ∀ {a b : V}, a ≤ b → b ≤ a → a = b
  zero_le : ∀ a : V, 0 ≤ a
  zero_add : ∀ a : V, 0 + a = a
  add_comm : ∀ a b : V, a + b = b + a
  add_mono : ∀ {a b c d : V}, a ≤ b → c ≤ d → a + c ≤ b + d

/-- Costs counted in whole steps. -/
instance : Cost Nat where
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  le_antisymm := Nat.le_antisymm
  zero_le := Nat.zero_le
  zero_add := Nat.zero_add
  add_comm := Nat.add_comm
  add_mono := Nat.add_le_add

/-! ## Distance with a direction -/

/-- A distance that may differ in its two directions: a quasi-metric, or
Lawvere metric. `d a b` is how far `a` is from entailing `b`. -/
structure QMetric (α : Type) (V : Type) [Cost V] where
  /-- The distance from the first thing to the second. -/
  d : α → α → V
  /-- Nothing is at a distance from itself. -/
  self : ∀ a, d a a = 0
  /-- Going through a third thing is never shorter. -/
  triangle : ∀ a b c, d a c ≤ d a b + d b c

namespace QMetric

variable {α V : Type} [Cost V]

/-- `a` entails `b`: the distance from `a` to `b` is zero. -/
def Entails (m : QMetric α V) (a b : α) : Prop := m.d a b = 0

/-- `a` entails `b` up to the cost `ε`. -/
def Within (m : QMetric α V) (ε : V) (a b : α) : Prop := m.d a b ≤ ε

/-- `a` and `b` are equivalent: each entails the other. -/
def Equiv (m : QMetric α V) (a b : α) : Prop := m.Entails a b ∧ m.Entails b a

@[inherit_doc] notation:50 a " ⊑[" m "] " b => Entails m a b
@[inherit_doc] notation:50 a " ⊑[" m " ; " ε "] " b => Within m ε a b
@[inherit_doc] notation:50 a " ≡[" m "] " b => Equiv m a b

/-- Reflexivity: everything entails itself. -/
theorem entails_refl (m : QMetric α V) (a : α) : a ⊑[m] a := m.self a

/-- Transitivity: the triangle inequality at zero is the chaining of two
entailments. -/
theorem entails_trans (m : QMetric α V) {a b c : α}
    (hab : a ⊑[m] b) (hbc : b ⊑[m] c) : a ⊑[m] c := by
  have h : m.d a c ≤ 0 := by
    have t := m.triangle a b c
    rw [show m.d a b = 0 from hab, show m.d b c = 0 from hbc, Cost.zero_add] at t
    exact t
  exact Cost.le_antisymm h (Cost.zero_le _)

/-- Entailment is entailment up to the cost zero. -/
theorem entails_iff_within_zero (m : QMetric α V) (a b : α) :
    (a ⊑[m] b) ↔ (a ⊑[m ; 0] b) :=
  ⟨fun h => by
      show m.d a b ≤ 0
      rw [show m.d a b = 0 from h]
      exact Cost.le_refl 0,
   fun h => Cost.le_antisymm h (Cost.zero_le _)⟩

/-- Graded transitivity: the costs of two steps add. -/
theorem within_trans (m : QMetric α V) {a b c : α} {ε δ : V}
    (hab : a ⊑[m ; ε] b) (hbc : b ⊑[m ; δ] c) : a ⊑[m ; ε + δ] c :=
  Cost.le_trans (m.triangle a b c) (Cost.add_mono hab hbc)

/-- A looser bound still holds. -/
theorem within_weaken (m : QMetric α V) {a b : α} {ε δ : V}
    (h : a ⊑[m ; ε] b) (hle : ε ≤ δ) : a ⊑[m ; δ] b :=
  Cost.le_trans h hle

theorem equiv_refl (m : QMetric α V) (a : α) : a ≡[m] a :=
  ⟨m.entails_refl a, m.entails_refl a⟩

theorem equiv_symm (m : QMetric α V) {a b : α} (h : a ≡[m] b) : b ≡[m] a :=
  ⟨h.2, h.1⟩

theorem equiv_trans (m : QMetric α V) {a b c : α}
    (hab : a ≡[m] b) (hbc : b ≡[m] c) : a ≡[m] c :=
  ⟨m.entails_trans hab.1 hbc.1, m.entails_trans hbc.2 hab.2⟩

/-- The same distance read backwards. If `m` measures `is-a`, then `m.op`
measures `generalizes`. -/
def op (m : QMetric α V) : QMetric α V where
  d a b := m.d b a
  self := m.self
  triangle a b c := by
    have t := m.triangle c b a
    rw [Cost.add_comm] at t
    exact t

/-- Reversing the distance reverses the entailment. -/
theorem op_entails (m : QMetric α V) (a b : α) : (a ⊑[m.op] b) ↔ (b ⊑[m] a) :=
  Iff.rfl

/-! ## Why a symmetric distance is not enough -/

/-- Under a symmetric distance, whatever entails is entailed back. -/
theorem entails_symm_of_symm (m : QMetric α V) (sym : ∀ a b, m.d a b = m.d b a)
    {a b : α} (h : a ⊑[m] b) : b ⊑[m] a := by
  show m.d b a = 0
  rw [← sym a b]
  exact h

/-- Under a symmetric distance, entailment and equivalence are one relation:
an ordinary metric can say that two things are the same and nothing else. -/
theorem entails_iff_equiv_of_symm (m : QMetric α V)
    (sym : ∀ a b, m.d a b = m.d b a) (a b : α) : (a ⊑[m] b) ↔ (a ≡[m] b) :=
  ⟨fun h => ⟨h, m.entails_symm_of_symm sym h⟩, fun h => h.1⟩

end QMetric

/-! ## Derivation -/

/-- A chain of asserted steps from one thing to another, with its total cost.
`E a b c` says that a step from `a` to `b` of cost `c` is asserted. -/
inductive Chain {α V : Type} [Cost V] (E : α → α → V → Prop) : α → α → V → Prop
  /-- The empty chain costs nothing. -/
  | nil (a : α) : Chain E a a 0
  /-- One asserted step, then a chain. -/
  | cons {a b z : α} {c₁ c₂ : V} : E a b c₁ → Chain E b z c₂ → Chain E a z (c₁ + c₂)

namespace Chain

variable {α V : Type} [Cost V] {E : α → α → V → Prop}

/-- Soundness of derivation: in any distance that respects the asserted
steps, a chain of total cost `c` puts its ends within `c`. -/
theorem sound (m : QMetric α V) (respects : ∀ a b c, E a b c → m.d a b ≤ c)
    {a z : α} {c : V} (h : Chain E a z c) : a ⊑[m ; c] z := by
  induction h with
  | nil a =>
    show m.d a a ≤ 0
    rw [m.self a]
    exact Cost.le_refl 0
  | cons e _ ih => exact m.within_trans (respects _ _ _ e) ih

/-- A chain that costs nothing is an entailment. -/
theorem sound_zero (m : QMetric α V) (respects : ∀ a b c, E a b c → m.d a b ≤ c)
    {a z : α} (h : Chain E a z 0) : a ⊑[m] z :=
  (m.entails_iff_within_zero a z).mpr (sound m respects h)

end Chain

/-! ## A preorder is a distance with two values -/

/-- The two costs of classical logic: an entailment holds, at no cost, or it
fails, at a cost nothing exceeds. -/
inductive Truth
  | holds
  | fails
  deriving DecidableEq

namespace Truth

/-- `holds` is below everything, and everything is below `fails`. -/
def le : Truth → Truth → Prop
  | fails, holds => False
  | _, _ => True

/-- Adding costs is conjunction: the sum holds when both parts hold. -/
def add : Truth → Truth → Truth
  | holds, holds => holds
  | _, _ => fails

instance : Cost Truth where
  le := le
  add := add
  zero := holds
  le_refl a := by cases a <;> trivial
  le_trans {a b c} h₁ h₂ := by cases a <;> cases b <;> cases c <;> trivial
  le_antisymm {a b} h₁ h₂ := by cases a <;> cases b <;> first | rfl | exact h₁.elim | exact h₂.elim
  zero_le a := by cases a <;> trivial
  zero_add a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_mono {a b c d} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;> cases d <;> first | trivial | exact h₁.elim | exact h₂.elim

end Truth

/-- A reflexive and transitive relation. -/
structure Preorder' (α : Type) where
  /-- The relation. -/
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

/-- Every distance gives a preorder: its entailment. -/
def QMetric.toPreorder {α V : Type} [Cost V] (m : QMetric α V) : Preorder' α where
  le := m.Entails
  refl := m.entails_refl
  trans := m.entails_trans

open Classical in
/-- Every preorder gives a distance with two values: `holds` where the
relation holds and `fails` where it does not. -/
noncomputable def Preorder'.toQMetric {α : Type} (r : Preorder' α) : QMetric α Truth where
  d a b := if r.le a b then Truth.holds else Truth.fails
  self a := by simp [r.refl a]; rfl
  triangle a b c := by
    by_cases hab : r.le a b <;> by_cases hbc : r.le b c
    · simp [hab, hbc, r.trans hab hbc]; trivial
    all_goals
      simp only [hab, hbc, ite_true, ite_false]
      by_cases hac : r.le a c <;> simp only [hac, ite_true, ite_false] <;> trivial

open Classical in
/-- The two constructions undo each other: the entailment of the distance
built from a preorder is that preorder. -/
theorem Preorder'.toQMetric_entails {α : Type} (r : Preorder' α) (a b : α) :
    (a ⊑[r.toQMetric] b) ↔ r.le a b := by
  show (if r.le a b then Truth.holds else Truth.fails) = Truth.holds ↔ r.le a b
  by_cases h : r.le a b <;> simp [h]

/-! ## Why a signed distance is too much -/

/-- A signed distance: one number for each pair, which changes sign when the
pair is turned around. -/
structure Signed (α : Type) where
  /-- The signed distance from the first thing to the second. -/
  s : α → α → Int
  /-- Turning the pair around changes the sign. -/
  anti : ∀ a b, s b a = -s a b

namespace Signed

variable {α : Type}

/-- Reading "the distance from `a` to `b` is not negative" as "`a` entails
`b`", every two things are comparable. Nothing can be unrelated. -/
theorem total (m : Signed α) (a b : α) : 0 ≤ m.s a b ∨ 0 ≤ m.s b a := by
  have := m.anti a b
  omega

/-- If signed distances also add up along a path, every distance is a
difference of heights above one chosen thing: the space is a line. -/
theorem potential (m : Signed α) (additive : ∀ a b c, m.s a c = m.s a b + m.s b c)
    (o a b : α) : m.s a b = m.s o b - m.s o a := by
  have := additive o a b
  omega

end Signed

end DistanceLogic
