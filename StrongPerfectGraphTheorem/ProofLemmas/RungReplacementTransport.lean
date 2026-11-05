module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.ProofLemmas.Thm75Setup
public import StrongPerfectGraphTheorem.ProofLemmas.AppearanceVertexTypeTransport

/-!
# Moving the labelled data of an appearance along an isomorphism of the subdivision

This is a step of the rung replacement in the proof of 7.5 that
`Thm75Claim2Transport` does not already provide: the cliques `Nv` of an appearance transport
along an isomorphism `χ` of the underlying subdivision.  The final step of the construction
builds `H'` on a sum type and must present it on `Fin m`, and the labelled output of 7.5(2)
consists precisely of clique equations, so they have to travel with the graph.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.RungReplacementTransport

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.ProofLemmas.Thm75Setup

variable {V α β : Type*}

/-- The clique `Nv` of an appearance is unchanged when the subdivision is renamed. -/
theorem nset_map {A : SimpleGraph α} {B : SimpleGraph β} (χ : A ≃g B)
    {G : SimpleGraph V} {K : Set V} (φ : A.lineGraph ≃g G.induce K) (z : α) :
    NSet G B K ((Thm75Claim2Transport.lineGraphIso χ).symm.trans φ) (χ z) = NSet G A K φ z := by
  ext x
  constructor
  · rintro ⟨e', he', hinc, rfl⟩
    have heA : Sym2.map χ.symm e' ∈ A.edgeSet :=
      Thm75Claim2Transport.map_mem_edgeSet χ.symm e' he'
    have hmap : Sym2.map χ (Sym2.map χ.symm e') = e' := Thm75Claim2Transport.sym2_map_symm' χ e'
    have hinc' : Sym2.map χ.symm e' ∈ incidentEdges A z := by
      rw [← Thm75Claim2Transport.mem_incidentEdges_map χ z, hmap]
      exact hinc
    refine ⟨Sym2.map χ.symm e', heA, hinc', ?_⟩
    have hb := Thm75Claim2Transport.phi_bridge χ φ (Sym2.map χ.symm e') heA
    rw [show (⟨Sym2.map χ (Sym2.map χ.symm e'),
      Thm75Claim2Transport.map_mem_edgeSet χ (Sym2.map χ.symm e') heA⟩ : B.edgeSet)
        = ⟨e', he'⟩ from Subtype.ext hmap] at hb
    exact hb.symm
  · rintro ⟨e, he, hinc, rfl⟩
    refine ⟨Sym2.map χ e, Thm75Claim2Transport.map_mem_edgeSet χ e he,
      (Thm75Claim2Transport.mem_incidentEdges_map χ z e).mpr hinc, ?_⟩
    exact (Thm75Claim2Transport.phi_bridge χ φ e he).symm

end StrongPerfectGraphTheorem.ProofLemmas.RungReplacementTransport
