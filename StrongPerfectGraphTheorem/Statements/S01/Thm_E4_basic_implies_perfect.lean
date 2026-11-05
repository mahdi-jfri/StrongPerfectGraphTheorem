module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Replication
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.ProofLemmas.BipartitePerfect
public import StrongPerfectGraphTheorem.ProofLemmas.LineGraphBipartitePerfect
public import StrongPerfectGraphTheorem.ProofLemmas.DoubleSplitPerfect
public import StrongPerfectGraphTheorem.ProofLemmas.DoubleSplitSelfComplementary
public import StrongPerfectGraphTheorem.ProofLemmas.IsoTransport
public import StrongPerfectGraphTheorem.Statements.S01.Thm_1_1

@[expose] public section

set_option linter.unusedSectionVars false

namespace StrongPerfectGraphTheorem.MainTheorem

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Decompositions
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.Replication
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **E4** — "every basic graph is perfect".  Bipartite: trivial.  Line graph of a
bipartite graph: König.  Double split: the reader.  Complements: Lovász' 1.1
(except for the double split case, which is self-complementary). -/
theorem thm_E4_basic_implies_perfect (G : SimpleGraph V) (hG : SPGT.IsBasic G) :
    SPGT.IsPerfect G := by
  classical
  -- perfection of the complement transfers back along `Gᶜᶜ = G` by 1.1 (Lovász).
  have hcompl : ∀ K : SimpleGraph V, StrongPerfectGraphTheorem.Types.Core.SPGT.IsPerfect Kᶜ →
      StrongPerfectGraphTheorem.Types.Core.SPGT.IsPerfect K := by
    intro K hK
    have h := _root_.StrongPerfectGraphTheorem.MainTheorem.SPGT.thm_1_1 Kᶜ hK
    simpa using h
  rcases hG with (hb | hl | hd) | (hb | hl | hd)
  -- `G` bipartite.
  · exact _root_.StrongPerfectGraphTheorem.ProofLemmas.BipartitePerfect G hb
  -- `G` the line graph of a bipartite graph.
  · obtain ⟨n, H, hHbip, ⟨e⟩⟩ := hl
    exact (_root_.StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.isPerfect_iso e).mpr
      (_root_.StrongPerfectGraphTheorem.ProofLemmas.LineGraphBipartitePerfect H hHbip)
  -- `G` a double split graph.
  · exact _root_.StrongPerfectGraphTheorem.ProofLemmas.DoubleSplitPerfect G hd
  -- `Gᶜ` bipartite.
  · exact hcompl G (_root_.StrongPerfectGraphTheorem.ProofLemmas.BipartitePerfect Gᶜ hb)
  -- `Gᶜ` the line graph of a bipartite graph.
  · obtain ⟨n, H, hHbip, ⟨e⟩⟩ := hl
    exact hcompl G ((_root_.StrongPerfectGraphTheorem.ProofLemmas.IsoTransport.isPerfect_iso e).mpr
      (_root_.StrongPerfectGraphTheorem.ProofLemmas.LineGraphBipartitePerfect H hHbip))
  -- `Gᶜ` a double split graph; then so is `Gᶜᶜ = G`, and no appeal to 1.1 is needed.
  · have hGd : StrongPerfectGraphTheorem.Types.BasicClasses.SPGT.IsDoubleSplitGraph G := by
      have h := _root_.StrongPerfectGraphTheorem.ProofLemmas.DoubleSplitSelfComplementary.isDoubleSplitGraph_compl hd
      simpa using h
    exact _root_.StrongPerfectGraphTheorem.ProofLemmas.DoubleSplitPerfect G hGd

end SPGT

end StrongPerfectGraphTheorem.MainTheorem
