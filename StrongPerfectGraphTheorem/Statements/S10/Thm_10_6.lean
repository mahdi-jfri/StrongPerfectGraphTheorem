module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.ProofLemmaStatements.HyperprismLocalAttachmentsOrBalancedSkew
public import StrongPerfectGraphTheorem.ProofLemmas.Thm106Steps

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S10

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_10_6 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (heven : ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃) :
    ((∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃ ∧
        {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} = Set.univ) ∧
      Fintype.card V = 9) ∨
    AdmitsProper2Join G ∨ AdmitsBalancedSkewPartition G := by
  apply StrongPerfectGraphTheorem.ProofLemmas.Thm106Steps.thm_10_6_of_claim2 G hG hK4
  · intro hG' hK4' A B C hH hmax
    exact
      StrongPerfectGraphTheorem.ProofLemmaStatements.HyperprismLocalAttachmentsOrBalancedSkew.hyperprismLocalAttachmentsOrBalancedSkew
        G hG' hK4' A B C hH hmax
  · exact heven

end SPGT

end StrongPerfectGraphTheorem.Statements.S10
