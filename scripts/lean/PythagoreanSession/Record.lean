/-!
# The observer's counts

Alice closed Act 2 with tables: which of Percy's 37 facts each proof uses,
how much two proofs share, and which proof falls when a fact is taken
away. This file takes her translation of the three "Used" lists into
Percy's numbers as given, and checks every count and every row that
follows from it. Whether the translation itself is right is a matter of
reading and is not checked.
-/

namespace PythagoreanSession.Record

/-- The facts of the common ground each proof uses, by Percy's numbers. -/
def bob : List Nat :=
  [1, 2, 4, 6, 8, 10, 11, 13, 17, 19, 20, 24, 25, 26, 27, 32, 34, 35, 37]
def dave : List Nat :=
  [1, 6, 8, 10, 14, 16, 17, 19, 20, 28, 29, 30, 31, 32, 33, 34, 36]
def carol : List Nat := [1, 4, 5, 6, 7, 8, 9, 15, 16, 17, 20, 22, 23]

/-- Percy's marks: the facts that are false in the town. -/
def falseInTown : List Nat := [19, 21, 23, 33, 35, 36, 37]
/-- Percy's marks: the facts that are false, empty or fallen on the ball. -/
def notOnBall : List Nat :=
  [10, 11, 15, 18, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 35, 36, 37]

def both (xs ys : List Nat) : List Nat := xs.filter (ys.contains ·)
def either (xs ys : List Nat) : List Nat := xs ++ ys.filter (!xs.contains ·)
def only (xs ys zs : List Nat) : List Nat :=
  xs.filter (fun g => !ys.contains g && !zs.contains g)

/-- 19, 17 and 13 facts, 33 of the 37 used by at least one proof, and the
four unused are G3, G12, G18 and G21. -/
theorem how_many_facts :
    bob.length = 19 ∧ dave.length = 17 ∧ carol.length = 13 ∧
      (either (either bob dave) carol).length = 33 ∧
      (List.range' 1 37).filter (!(either (either bob dave) carol).contains ·)
        = [3, 12, 18, 21] := by
  decide

/-- The table "What each proof stands on". -/
theorem what_each_proof_stands_on :
    both (both bob dave) carol = [1, 6, 8, 17, 20] ∧
    (both bob dave).filter (!carol.contains ·) = [10, 19, 32, 34] ∧
    (both bob carol).filter (!dave.contains ·) = [4] ∧
    (both dave carol).filter (!bob.contains ·) = [16] ∧
    (only bob dave carol).length = 9 ∧ (only dave bob carol).length = 7 ∧
    (only carol bob dave).length = 6 := by
  decide

/-- The shares: 9 of 27, 6 of 24 and 6 of 26, which round to 0.33, 0.25 and
0.23. -/
theorem shares :
    ((both bob dave).length = 9 ∧ (either bob dave).length = 27) ∧
    ((both dave carol).length = 6 ∧ (either dave carol).length = 24) ∧
    ((both bob carol).length = 6 ∧ (either bob carol).length = 26) ∧
    (33 * 27 ≤ 100 * 9 ∧ 100 * 9 < 34 * 27) ∧ 25 * 24 = 100 * 6 ∧
    (23 * 26 ≤ 100 * 6 ∧ 100 * 6 < 24 * 26) := by
  decide

/-- The table "Take a fact away: which proofs fall?". A proof falls when it
uses the fact. Each row is the fact and Alice's three entries. -/
theorem take_a_fact_away :
    [(20, true, true, true), (17, true, true, true), (19, true, true, false),
      (32, true, true, false), (34, true, true, false), (24, true, false, false),
      (33, false, true, false), (23, false, false, true), (22, false, false, true),
      (16, false, true, true)].all
      (fun (g, b, d, c) => bob.contains g == b && dave.contains g == d &&
        carol.contains g == c) = true := by
  decide

/-- The counts in the closings: 44 assumptions, 68 steps, 47 of them Bob's
and Dave's, seven new items, and 37 facts of which 4 are unused. -/
theorem counts :
    14 + 15 + 15 = 44 ∧ 22 + 25 + 21 = 68 ∧ 22 + 25 = 47 ∧ 3 + 1 + 3 = 7 ∧
      37 - 33 = 4 := by
  decide

/-! ## Three disputes the counts decide -/

/-- Percy's open question: does Bob add lengths along a slanted line? By
Alice's translation he does not use G16 at all. Reading his steps agrees:
the only lengths he reads are along the axes (`Bob.step3_axis_lengths`),
and the length `c` reaches the grid through side-angle-side. -/
theorem bob_does_not_add_lengths : bob.contains 16 = false := by
  decide

/-- Percy, before reading the proofs: "Dave keeps the town out with G21",
that a figure can be moved. Dave's proof does not use G21. What keeps the
town out, for Bob and Dave, is side-angle-side, and for Carol G23. Every
proof uses a fact that is false in the town and a fact that fails on the
ball. -/
theorem what_keeps_the_town_out :
    dave.contains 21 = false ∧
    both bob falseInTown = [19, 35, 37] ∧ both dave falseInTown = [19, 33, 36] ∧
    both carol falseInTown = [23] ∧
    (both bob notOnBall).length = 9 ∧ (both dave notOnBall).length = 7 ∧
    both carol notOnBall = [15, 20, 22, 23] := by
  decide

/-- Alice's own caution: the shares depend on how finely the facts are
split. Percy split Dave's item 10 into G28 to G31. Counted as one fact, the
share of Bob and Dave is 9 of 24 and not 9 of 27, and that of Dave and
Carol 6 of 21 and not 6 of 24. -/
theorem shares_depend_on_the_split :
    let dave' := dave.filter (fun g => g != 29 && g != 30 && g != 31)
    (both bob dave').length = 9 ∧ (either bob dave').length = 24 ∧
      (both dave' carol).length = 6 ∧ (either dave' carol).length = 21 := by
  decide

end PythagoreanSession.Record
