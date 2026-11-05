/-  **9.6** — the proof.

    The proof uses the paper's own parenthetical on printed p. 2, *"(Note that if `G` is a
    double split graph then so is `Ḡ`.)"*, which cites nothing.  It lives in the statement-free
    module `StrongPerfectGraphTheorem.ProofLemmas.DoubleSplitSelfComplementary`, not in
    `StrongPerfectGraphTheorem.ProofLemmas.RecalcitrantInF5` (which re-exports it).  The reason
    is the import order: `RecalcitrantInF5` imports
    `StrongPerfectGraphTheorem.Statements.S09.Thm_9_7`, which imports this module, so this
    module cannot import `RecalcitrantInF5`.  Nothing in the mathematics is circular: the
    paper's 9.7 cites 9.6, never the reverse. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Knots
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmas.Thm96Assembly
public import StrongPerfectGraphTheorem.ProofLemmas.DegenerateK4AppearanceYieldsStriation
public import StrongPerfectGraphTheorem.ProofLemmas.BipartiteK4AppearanceHasAtLeastEightVertices
public import StrongPerfectGraphTheorem.ProofLemmas.MaximalStriationForcesThm96Conclusion

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S09

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Knots StrongPerfectGraphTheorem.Types.Knots.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem thm_9_6 (G : SimpleGraph V) (hG : Berge G)
    (hdegG : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hdegGc : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hnoL33 : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)) :
    IsDoubleSplitGraph G ∨
    AdmitsBalancedSkewPartition G ∨
    (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨
    (¬ Appears G (⊤ : SimpleGraph (Fin 4)) ∧ ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4))) := by
  exact StrongPerfectGraphTheorem.ProofLemmas.Thm96Assembly.thm_9_6_of_steps G hG hdegG hdegGc hnoL33
    (fun Gx => StrongPerfectGraphTheorem.ProofLemmas.DegenerateK4AppearanceYieldsStriation.degenerateK4AppearanceYieldsStriation Gx)
    (fun Gx => StrongPerfectGraphTheorem.ProofLemmas.BipartiteK4AppearanceHasAtLeastEightVertices.BipartiteK4AppearanceHasAtLeastEightVertices Gx)
    (fun Gx => StrongPerfectGraphTheorem.ProofLemmas.MaximalStriationForcesThm96Conclusion.maximalStriationForcesThm96Conclusion Gx)


end SPGT

end StrongPerfectGraphTheorem.Statements.S09
