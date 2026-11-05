module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.Pseudowheels
public import StrongPerfectGraphTheorem.Types.WheelSystems
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.ProofLemmas.WheelSystemBasics
public import StrongPerfectGraphTheorem.ProofLemmas.Thm213Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm213Steps

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S21

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.Pseudowheels StrongPerfectGraphTheorem.Types.Pseudowheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

open StrongPerfectGraphTheorem.ProofLemmas.Thm213Setup StrongPerfectGraphTheorem.ProofLemmas.Thm213Steps

/-- **21.3** — the paper's proof, verbatim in structure:

*Suppose there is no such wheel.  Choose `r` with `1 ≤ r ≤ t`, minimum such that `x_{t+1}` has a
neighbour in `A_r` and a nonneighbour in `X_r`.  By hypothesis, every member of `Y` has a
neighbour in `A_r ∪ {x_{t+1}}`.  By 19.2, `r > 1`.  Since at most one member of `Y` has no
neighbour in `A_{r−1}` (because at most one has no neighbour in `A_1`), it follows from 21.2 that
`x_{t+1}` has a neighbour in `A_{r−1}`.  Since no wheel has hub `Y`, 20.1 implies that
`x_0,…,x_r,x_{t+1}` is not a `Y`-diamond, and so `x_{t+1}` is not `X_{r−1}`-complete.  But that
contradicts the minimality of `r`.* -/
theorem thm_21_3 (G : SimpleGraph V) (hG : InF8 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (x : ℕ → V) (t : ℕ) (Y : Set V) (ht : 1 ≤ t)
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) Y)
    (hone : Set.Subsingleton
      {y ∈ Y | VertexAnticomplete G y (wheelSystemA G z A₀ x 1)})
    (hr : ∀ r : ℕ, 1 ≤ r → r ≤ t →
      IsWheelSystem G z A₀ (fun j => if j ≤ r then x j else x (t + 1)) (r + 1) →
        ∀ y ∈ Y, ∃ a ∈ (wheelSystemA G z A₀ x r ∪ {x (t + 1)} : Set V), G.Adj y a) :
    ∃ C : List V, IsWheel G C Y := by
  classical
  -- *"Suppose there is no such wheel."*
  by_contra hno
  -- *"Choose `r` with `1 ≤ r ≤ t`, minimum such that `x_{t+1}` has a neighbour in `A_r` and a
  -- nonneighbour in `X_r`."*  Such an `r` exists: `r = t` works, by conditions 2 and 3 of the
  -- wheel-system definition applied at `i = t+1`.
  have htp := top_property hhub.1 ht
  have hex : ∃ r : ℕ, 1 ≤ r ∧ r ≤ t ∧
      (∃ a ∈ wheelSystemA G z A₀ x r, G.Adj (x (t + 1)) a) ∧
      ¬ VertexComplete G (x (t + 1)) (wheelSystemX x r) :=
    ⟨t, ht, le_rfl, htp.1, htp.2⟩
  obtain ⟨r, ⟨hr1, hrt, hnbA, hncX⟩, hmin⟩ :
      ∃ r : ℕ, (1 ≤ r ∧ r ≤ t ∧
          (∃ a ∈ wheelSystemA G z A₀ x r, G.Adj (x (t + 1)) a) ∧
          ¬ VertexComplete G (x (t + 1)) (wheelSystemX x r)) ∧
        ∀ m : ℕ, m < r → ¬ (1 ≤ m ∧ m ≤ t ∧
          (∃ a ∈ wheelSystemA G z A₀ x m, G.Adj (x (t + 1)) a) ∧
          ¬ VertexComplete G (x (t + 1)) (wheelSystemX x m)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  -- `x₀,…,x_r,x_{t+1}` is a wheel system of height `r+1`, with hub `Y`.
  have hagree : ∀ j ≤ r, (fun j => if j ≤ r then x j else x (t + 1)) j = x j :=
    fun j hj => if_pos hj
  have htop : (fun j => if j ≤ r then x j else x (t + 1)) (r + 1) = x (t + 1) :=
    if_neg (by omega)
  have hws' : IsWheelSystem G z A₀ (fun j => if j ≤ r then x j else x (t + 1)) (r + 1) :=
    isWheelSystem_of_agrees hhub.1 hr1 hrt hagree htop hnbA hncX
  have hhub' : IsHubForWheelSystem G z A₀ (fun j => if j ≤ r then x j else x (t + 1)) (r + 1) Y :=
    isHub_of_agrees hhub hr1 hrt hagree htop hnbA hncX
  -- *"By hypothesis, every member of `Y` has a neighbour in `A_r ∪ {x_{t+1}}`."*
  have hnbr : ∀ y ∈ Y, ∃ a ∈ (wheelSystemA G z A₀ x r ∪ {x (t + 1)} : Set V), G.Adj y a :=
    hr r hr1 hrt hws'
  -- *"By 19.2, `r > 1`."*
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · exfalso
      have hr' : r = 1 := by omega
      subst hr'
      exact hno (wheel_of_r_eq_one hG.1 hframe ht hhub _ hagree htop hws' hnbr)
    · exact hge
  -- *"... it follows from 21.2 that `x_{t+1}` has a neighbour in `A_{r−1}`."*
  have hprev : ∃ a ∈ wheelSystemA G z A₀ x (r - 1), G.Adj (x (t + 1)) a :=
    nbr_in_prev hG hframe hr2 hrt _ hagree htop hhub' hone hnbr hno
  -- *"Since no wheel has hub `Y`, 20.1 implies that `x₀,…,x_r,x_{t+1}` is not a `Y`-diamond, and
  -- so `x_{t+1}` is not `X_{r−1}`-complete."*
  have hncprev : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x (r - 1)) :=
    not_complete_prev hG.1 hframe hr2 hrt _ hagree htop hhub' hprev hno
  -- *"But that contradicts the minimality of `r`."*
  exact hmin (r - 1) (by omega) ⟨by omega, by omega, hprev, hncprev⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S21
