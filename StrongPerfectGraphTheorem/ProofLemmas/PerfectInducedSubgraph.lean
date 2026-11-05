module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.ProofLemmas.IsoTransport

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas

open StrongPerfectGraphTheorem.Types.Core.SPGT

/-- Every induced subgraph of a finite perfect graph is perfect. -/
theorem PerfectInducedSubgraph
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y : Set W)
    (hK : IsPerfect K) :
    IsPerfect (K.induce Y) := by
  classical
  intro X
  let e : (K.induce Y).induce X ≃g K.induce (Subtype.val '' X) :=
    { Equiv.Set.image (Subtype.val : Y → W) X Subtype.val_injective with
      map_rel_iff' := by
        intro a b
        rfl }
  rw [StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.chromaticNumber_iso e,
    StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.cliqueNum_iso e]
  exact hK (Subtype.val '' X)

end StrongPerfectGraphTheorem.ProofLemmas
