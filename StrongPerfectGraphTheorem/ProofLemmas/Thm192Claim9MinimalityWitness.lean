module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.WheelSystems
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim9MinimalityWitnessRepaired

/-!
# The minimality witness in claim (9) of 19.2

This file isolates one sentence from the printed proof whose use is sensitive to the
project's repaired order of the two extremal choices.

## Repaired statement

The statement below has two hypotheses that the printed sentence lacks, `hyY : y ∈ Y` and
`h2y : ¬ G.Adj y (x 2)`.  Without them the argument breaks: the project minimises over
`Thm192Setup.GoodA`, which carries the extra clause *"`y` has a neighbour in `A`"*, so
`A \ {f}` may fail to be `GoodA` at that clause rather than at the `Y`-clause, and then no
`y₀` need exist.

Adding `¬ G.Adj y (x 2)` is the smallest repair: when `y` is nonadjacent to `x₂`, the
`y`-clause of `GoodA` is a *special case* of its `Y`-clause, so the two ways `A \ {f}` can
fail to be `GoodA` collapse into the single printed one, with `y₀ = y`.  The case
`G.Adj y (x 2)` is handled separately by the caller (`Thm192Claim9YAdjX2`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim9MinimalityWitness

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (19.2, claim (9), printed p. 121):

*"Choose `f ∈ A \ F` such that `A \ {f}` is connected. From the minimality of `A`,
there exists `y₀ ∈ Y` nonadjacent to `x₂` with no neighbour in `A \ {f}`."*

The conclusion packages those two consecutive sentences.  The hypotheses `hyY` and `h2y`
are the repair described in the module header. -/
theorem minimalityWitness (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V)
    (Y : Set V) (y : V) (hyY : y ∈ Y) (h2y : ¬ G.Adj y (x 2))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (F : Set V) (hFA : F ⊆ A) (hFconn : ConnectedSet G F) (hFne : F ≠ A)
    (hF0 : ∃ a ∈ F, G.Adj (x 0) a) (hF1 : ∃ a ∈ F, G.Adj (x 1) a)
    (hF2 : ∃ a ∈ F, G.Adj (x 2) a) :
    ∃ f ∈ A \ F, ConnectedSet G (A \ {f}) ∧
      ∃ y₀ ∈ Y, ¬ G.Adj y₀ (x 2) ∧ VertexAnticomplete G y₀ (A \ {f}) := by
  obtain ⟨f, hf, hconn, hdisj⟩ :=
    Thm192Claim9MinimalityWitnessRepaired.minimalityWitness G z A₀ x Y y A hA hAmin
      F hFA hFconn hFne hF0 hF1 hF2
  refine ⟨f, hf, hconn, ?_⟩
  rcases hdisj with h | h
  · exact h
  · exact ⟨y, hyY, h2y, h⟩

end StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim9MinimalityWitness
