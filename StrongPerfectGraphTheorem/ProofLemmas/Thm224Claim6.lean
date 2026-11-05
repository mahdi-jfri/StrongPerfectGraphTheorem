module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.WheelSystems
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.ProofLemmas.Thm224ClaimsDefs
public import StrongPerfectGraphTheorem.ProofLemmas.Thm224Claim6LongAntipathEven
public import StrongPerfectGraphTheorem.ProofLemmas.Thm224Claim6OddAntipathForcesZConflict

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm224Claim6

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm224Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(6)** *"If `x_{t+1}` is adjacent to `u₁` then `u₁` is `X_t`-complete."* -/
theorem claim6 {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length) :
    ∀ u₁ ∈ u.head?, G.Adj (x (t + 1)) u₁ → VertexComplete G u₁ (wheelSystemX x t) := by
  classical
  intro u₁ hu₁ hqu₁
  rcases u with _ | ⟨v, vs⟩
  · simp at hu₁
  · simp only [List.head?_cons, Option.mem_some_iff] at hu₁
    subst v
    rcases vs with _ | ⟨u₂, r⟩
    · have he := Nat.even_iff.mp hlen
      simp at he
    · by_contra hu₁notX
      obtain ⟨L, hL, hLint, hext, _hlarge, heven, havoid⟩ :=
        StrongPerfectGraphTheorem.ProofLemmas.Thm224Claim6LongAntipathEven.thm224Claim6LongAntipathEven
          hG hopt hT hTshape hA₀ hhub hcon hu hlen rfl hqu₁ hu₁notX
      exact
        StrongPerfectGraphTheorem.ProofLemmas.Thm224Claim6OddAntipathForcesZConflict.thm224Claim6OddAntipathForcesZConflict
          hG hopt hT hTshape hA₀ hhub hcon hu hlen rfl hL hLint hext heven havoid

end StrongPerfectGraphTheorem.ProofLemmas.Thm224Claim6
