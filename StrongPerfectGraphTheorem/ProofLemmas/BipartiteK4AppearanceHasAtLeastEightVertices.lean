/-  Proof of the 9.6 leaf `BipartiteK4AppearanceHasAtLeastEightVertices`.

PAPER (9.6, printed p. 55): *"We may assume that there is an appearance of `K₄` in one of
`G, Ḡ`, and consequently `|V(G)| ≥ 8`."*

The counting behind the *"consequently"* — a bipartite subdivision of `K₄` has at least eight
edges, and the vertex set of the appearance is in bijection with that edge set through the
isomorphism `L(H) ≃g G|K` — is already carried out in
`StrongPerfectGraphTheorem.ProofLemmas.K4AppearanceEightVertices`; this file is the one-line consequence. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.K4AppearanceEightVertices

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.BipartiteK4AppearanceHasAtLeastEightVertices

open StrongPerfectGraphTheorem.Types.Appearances.SPGT

theorem BipartiteK4AppearanceHasAtLeastEightVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (happears : Appears G (⊤ : SimpleGraph (Fin 4))) :
    8 ≤ Nat.card V :=
  StrongPerfectGraphTheorem.ProofLemmas.K4AppearanceEightVertices.eight_le_card_of_appears G happears

end StrongPerfectGraphTheorem.ProofLemmas.BipartiteK4AppearanceHasAtLeastEightVertices
