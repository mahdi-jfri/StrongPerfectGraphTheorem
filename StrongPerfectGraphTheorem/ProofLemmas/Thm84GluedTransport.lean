module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.IsoTransport
public import StrongPerfectGraphTheorem.ProofLemmas.SubdivisionCounting
public import StrongPerfectGraphTheorem.ProofLemmas.AppearanceVertexTypeTransport

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm84GluedTransport

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem glued_transport {U Wt : Type*} [Finite Wt]
    (G : SimpleGraph V) (J : SimpleGraph U) (K : Set V) (Hs : SimpleGraph Wt)
    (hsub : IsSubdivision J Hs) (hbip : Hs.IsBipartite)
    (hiso : Nonempty (Hs.lineGraph ≃g G.induce K)) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      IsBipartiteSubdivision J H ∧ Nonempty (H.lineGraph ≃g G.induce K) := by
  classical
  letI : Fintype Wt := Fintype.ofFinite Wt
  obtain ⟨H, ⟨ψ⟩⟩ := StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.exists_iso_fin Hs
  obtain ⟨φ⟩ := hiso
  exact ⟨Fintype.card Wt, H,
    Thm75Claim2Transport.isBipartiteSubdivision_map ψ ⟨hsub, hbip⟩,
    ⟨(Thm75Claim2Transport.lineGraphIso ψ).symm.trans φ⟩⟩

end StrongPerfectGraphTheorem.ProofLemmas.Thm84GluedTransport
