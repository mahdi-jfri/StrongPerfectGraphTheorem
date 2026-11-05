module

public import StrongPerfectGraphTheorem.ProofLemmas.Thm125Case2Finish
public import StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish
public import StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # Case (4) of Theorem 12.5 by left--right symmetry -/

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm125Case4

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Staircases StrongPerfectGraphTheorem.Types.Staircases.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Case (4), obtained from case (2) by exchanging the two strip ends and reversing both
the banister and the antipath. -/
theorem case4
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : ¬ G.Adj q₁ a₀) (hqkb₀ : G.Adj qk b₀) :
    IsLeftStar G A C B q₁ ∧ IsRightStar G A C B qk := by
  have hKswap :=
    StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.stronglyMaximalStaircase_swap.mp hK
  have hqrev : IsAntipathFrom G q.reverse qk q₁ :=
    StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathFrom_reverse hq
  have hqintSwap : ∀ w ∈ interior q.reverse,
      LeftDiagonal G B C A b₀ R₀.reverse a₀ w ∧
        RightDiagonal G B C A b₀ R₀.reverse a₀ w := by
    intro w hw
    have ho := hqint w (StrongPerfectGraphTheorem.ProofLemmas.PathBasics.mem_interior_reverse.mp hw)
    exact ⟨StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.rightDiagonal_swap.mp ho.2,
      StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.leftDiagonal_swap.mp ho.1⟩
  have hqkSwap : LeftDiagonal G B C A b₀ R₀.reverse a₀ qk ∧
      ¬ RightDiagonal G B C A b₀ R₀.reverse a₀ qk :=
    ⟨StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.rightDiagonal_swap.mp hqk.1,
      fun h => hqk.2 (StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.leftDiagonal_swap.mpr h)⟩
  have hq₁Swap : RightDiagonal G B C A b₀ R₀.reverse a₀ q₁ ∧
      ¬ LeftDiagonal G B C A b₀ R₀.reverse a₀ q₁ :=
    ⟨StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.leftDiagonal_swap.mp hq₁.1,
      fun h => hq₁.2 (StrongPerfectGraphTheorem.ProofLemmas.Thm125Case3Finish.rightDiagonal_swap.mpr h)⟩
  have hs := StrongPerfectGraphTheorem.ProofLemmas.Thm125Case2Finish.case2 G hG hK4 hprism hbreaker
    B C A b₀ a₀ R₀.reverse hKswap q.reverse qk q₁ hqrev hqintSwap hqkSwap hq₁Swap
      hqkb₀ hqa₀
  exact ⟨StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.isLeftStar_swap.mpr hs.2,
    StrongPerfectGraphTheorem.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mpr hs.1⟩

end StrongPerfectGraphTheorem.ProofLemmas.Thm125Case4
