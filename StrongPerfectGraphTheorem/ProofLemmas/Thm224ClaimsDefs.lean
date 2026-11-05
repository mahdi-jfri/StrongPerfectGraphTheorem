module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.WheelSystems

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm224Claims

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: *"Let `y-u₁-⋯-uₙ` be a minimal subpath of `T \ z` such that `uₙ` has a neighbour in
`A_t`; so `n > 0`.  From the maximality of `A_t` it follows that `uₙ` is `X_t`-complete …; and
since `T` is a tail it follows that none of `u₁,…,uₙ` are `Y`-complete."*

`u` is the list `u₁,…,uₙ`; `z :: y :: u` is a prefix of the tail `T`.  Minimality is recorded as
*"none of `u₁,…,u_{n−1}` has a neighbour in `A_t`"*, i.e. as a statement about `u.dropLast`. -/
def IsUPath (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) (Y : Set V)
    (T : List V) (y : V) (u : List V) : Prop :=
  z :: y :: u <+: T ∧
  u ≠ [] ∧
  (∀ un ∈ u.getLast?, (∃ a ∈ wheelSystemA G z A₀ x t, G.Adj un a) ∧
    VertexComplete G un (wheelSystemX x t)) ∧
  (∀ v ∈ u.dropLast, VertexAnticomplete G v (wheelSystemA G z A₀ x t)) ∧
  (∀ v ∈ u, ¬ VertexComplete G v Y)

end StrongPerfectGraphTheorem.ProofLemmas.Thm224Claims
