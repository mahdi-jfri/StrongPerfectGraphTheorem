module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim8Path
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim8Unique
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim8ZComplete
public import StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim8Endgame

/-!
# Claim (8) of 19.2: the one-sided statement

*"For assume `x₂` is nonadjacent to `y` and adjacent to `x₀` say."*  The four preceding
modules are chained here: the path `f₁-⋯-f_k` (`Thm192Claim8Path`), the two uniqueness
statements (`Thm192Claim8Unique`), *"`z` is `Y`-complete"* (`Thm192Claim8ZComplete`), and
the closing 2.10/13.6 contradiction (`Thm192Claim8Endgame`).

The *"say"* — i.e. the `x₀ ↔ x₁` symmetry — is discharged in `Thm192Claim8` itself, by
`Thm192Symmetry.sw`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim8Main

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"`x₂` is nonadjacent to `y` and adjacent to `x₀`"* is impossible. -/
theorem half (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      StrongPerfectGraphTheorem.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (h2y : ¬ G.Adj (x 2) y) (hx20 : G.Adj (x 2) (x 0)) :
    False := by
  obtain ⟨R, f₁, fk, hR, hRA, h0f₁, h2f₁, h1fk, hyfk, hfne⟩ :=
    Thm192Claim8Path.path_structure G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin hx20 h2y
  obtain ⟨hu2, hu1, hnuy⟩ :=
    Thm192Claim8Unique.unique_nbs G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      hcex hx20 h2y R f₁ fk hR hRA h0f₁ h2f₁ h1fk hyfk hfne
  have hzY : VertexComplete G z Y :=
    Thm192Claim8ZComplete.zComplete G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin hx20 h2y R f₁ fk hR hRA h0f₁ h2f₁ h1fk hyfk hfne hu2 hu1 hnuy
  exact Thm192Claim8Endgame.endgame G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
    hAmin hcex hx20 h2y R f₁ fk hR hRA h0f₁ h2f₁ h1fk hyfk hfne hu2 hu1 hzY

end StrongPerfectGraphTheorem.ProofLemmas.Thm192Claim8Main
