import PythagoreanSession.Cores
import PythagoreanSession.Bob
import PythagoreanSession.Dave
import PythagoreanSession.Carol
import PythagoreanSession.Percy
import PythagoreanSession.Disagreements
import PythagoreanSession.Record

/-!
# The Pythagoras classroom, checked

Lean proofs for the sides of discussion SLH-D-0005 and for the
disagreements between them. The verdicts, side by side, are in
`doc/discussion/SLH-D-0005-2026-11-23-0315-pear/leo.hmd`.

| File | Holds |
|---|---|
| `Cores.lean` | the algebra each of the three proofs ends on |
| `Bob.lean` | Bob's figure on the grid, step by step |
| `Dave.lean` | Dave's second cutting, and his proof at 60° |
| `Carol.lean` | Carol's angles, her foot of the perpendicular, scaling and shearing, and her proof at 60° |
| `Percy.lean` | the town, the ball, the world without √2, and the pictures that lie |
| `Disagreements.lean` | the distance formula, the grid and the length, the rules of area, side-angle-side |
| `Record.lean` | the observer's counts and tables |
| `Order.lean` | the facts about order the others need |

Everything is core Lean, with no library. The algebra is stated for an
arbitrary field or ordered field, so it holds for the real numbers. The
examples with numbers are stated for the integers or the fractions.

Check with `lake build` in `scripts/lean`. No proof contains `sorry`.
-/
