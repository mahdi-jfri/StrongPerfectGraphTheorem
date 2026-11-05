module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.WheelSystems
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.ProofLemmas.Thm233Descent

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S23

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.SkewTools StrongPerfectGraphTheorem.Types.SkewTools.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_23_3 (G : SimpleGraph V) (hG : InF9 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (s : ℕ) (hws : IsWheelSystem G z A₀ x s) :
    ¬ ∃ y : V,
        y ∉ insert z (wheelSystemX x s) ∧
        VertexComplete G y (insert z (wheelSystemX x s)) ∧
        (∃ a ∈ wheelSystemA G z A₀ x s, G.Adj y a) := by
  -- *"choose them with `s` minimum (it is important here that we minimize over all
  -- choices of the frame, not just of the wheel system)"* — run as strong induction
  -- on the height, with the frame, the base set and the sequence all quantified.
  have main : ∀ n : ℕ, ∀ (z' : V) (A' : Set V) (x' : ℕ → V),
      IsFrame G z' A' → IsWheelSystem G z' A' x' n →
      ¬ ∃ y : V,
          y ∉ insert z' (wheelSystemX x' n) ∧
          VertexComplete G y (insert z' (wheelSystemX x' n)) ∧
          (∃ a ∈ wheelSystemA G z' A' x' n, G.Adj y a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z' A' x' hf hw
      rintro ⟨y, hy₁, hy₂, hy₃⟩
      obtain ⟨r, -, hrn, hfr, hwr, hz₁, hz₂, hz₃⟩ :=
        StrongPerfectGraphTheorem.ProofLemmas.Thm233Descent.descent G hG hbsp z' A' hf x' n hw y hy₁ hy₂ hy₃
      exact ih r hrn y A' x' hfr hwr ⟨z', hz₁, hz₂, hz₃⟩
  exact main s z A₀ x hframe hws


end SPGT

end StrongPerfectGraphTheorem.Statements.S23
