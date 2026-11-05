# Counterexamples

This folder holds finite graphs that show where the printed paper is wrong. The proof of the
main theorem does not use them. The root module `StrongPerfectGraphTheorem.lean` imports them
only so that `lake build` checks them.

* `Thm93.lean` shows that **outcome 4 of 9.3 is false as printed**. It builds an 11-vertex
  graph that satisfies every hypothesis of
  `StrongPerfectGraphTheorem.Statements.S09.SPGT.thm_9_3`, and checks by computation that the
  printed conclusion fails (`printed_nine_three_false`). It also checks that the corrected
  conclusion, which the library proves, holds in this graph (`repaired_conclusion11`). So the
  printed clause is too strong, and the corrected clause is consistent with this example.

See `docs/NOTES_ON_THE_PAPER.md` at the root of the repository for the other places where the
Lean departs from the paper.
