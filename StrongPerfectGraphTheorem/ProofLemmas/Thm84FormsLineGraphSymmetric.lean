module

public import StrongPerfectGraphTheorem.ProofLemmas.FormsLineGraphForcesRungSymmetry

/-!
# Alias: a family of rungs that forms a line graph is edge-indexed

This module is a **thin re-export** of
`StrongPerfectGraphTheorem.ProofLemmas.FormsLineGraphForcesRungSymmetry.formsLineGraph_forces_rung_symmetry`,
kept because `StrongPerfectGraphTheorem/Statements/S08/Thm_8_4.lean` cites it under this name.  All the
mathematics, the passage of the paper it transcribes, the reason the on-the-nose form
`R u v = R v u` is **false**, the three lemmas `rung_end_unique`, `rung_ends_swap`,
`strip_inter_eq_union`, and the proof itself are documented in
`FormsLineGraphForcesRungSymmetry.lean`.  Do not duplicate content here.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm84FormsLineGraphSymmetric

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.StripSystems StrongPerfectGraphTheorem.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A choice of rungs that forms a line graph is edge-indexed**: reversing the orientation of an
edge of `J` reverses the chosen rung.  Alias for
`FormsLineGraphForcesRungSymmetry.formsLineGraph_forces_rung_symmetry`. -/
theorem formsLineGraph_symm {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H) :
    ∀ u v : U, J.Adj u v → R v u = (R u v).reverse :=
  StrongPerfectGraphTheorem.ProofLemmas.FormsLineGraphForcesRungSymmetry.formsLineGraph_forces_rung_symmetry
    G J hJ S N hSN H R hForms

end StrongPerfectGraphTheorem.ProofLemmas.Thm84FormsLineGraphSymmetric
