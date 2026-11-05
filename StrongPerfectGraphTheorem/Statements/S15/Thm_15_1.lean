/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 15. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas
public import StrongPerfectGraphTheorem.ProofLemmas.LooseSkewPartition
public import StrongPerfectGraphTheorem.ProofLemmas.Thm151Core
public import StrongPerfectGraphTheorem.Statements.S04.Thm_4_2

/-!
# Section 15 — Consequences

The seven numbered statements 15.1 – 15.7 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 92–95).
Every definition used here is imported, never restated:

* `StrongPerfectGraphTheorem.Types.Core` — `IsPathList`, `IsPathFrom`, `IsAntipathFrom`, `pathLength`,
  `SPGT.interior`, `IsHoleList`, `IsAntiholeList`, `holeLength`, `VertexComplete`,
  `Complete`, `ConnectedSet`, `AnticonnectedSet`, `IsAnticomponent`
* `StrongPerfectGraphTheorem.Types.Decompositions` — `AdmitsSkewPartition`, `AdmitsBalancedSkewPartition`
* `StrongPerfectGraphTheorem.Types.Classes` — `InF6` (printed p. 7: *"`F₆` is the class of all `G ∈ F₅` such
  that no induced subgraph of `G` is isomorphic to a double diamond"*)

Section 15 itself introduces **no new terminology**; every term occurring in 15.1–15.7 is
defined earlier in the paper, and each such term is imported from the module above that owns
it.

## Encoding conventions specific to this section

* A hole is the list `C` of its vertices in cyclic order (`IsHoleList`), and the paper's
  numbering *"with vertices `p₁, …, pₙ` in order"* is the list itself: `pₖ` is `C[k - 1]`.
* *"a path in `C`"* (15.5) — a subpath of the hole — is a path `P` of `G` whose vertices are
  a cyclically consecutive block of `C`, i.e. `∃ k, P <+: C.rotate k ∨ P.reverse <+: C.rotate k`
  (a path has no preferred direction, so both orientations of the block are allowed).  This is
  the convention already used by `StrongPerfectGraphTheorem.Types.Wheels.SPGT.IsSegment` for *"a path in a path
  or hole `H`"*.  The block consisting of the whole of `C` is automatically excluded, because a
  hole listed as a path list would have its two ends adjacent.
* *"`X ⊆ V(G) \ V(C)`"* is `∀ x ∈ X, x ∉ C`; *"`V(G) \ (X ∪ Y)`"* is the set complement
  `(X ∪ Y)ᶜ`.
* `SPGT.interior` is always written with its `SPGT.` prefix, since the bare name is captured
  by Mathlib's topological `interior`.
* *"`|S| > 1`"* is `Set.Nontrivial`; *"`|S| ≤ 2`"* is `S.ncard ≤ 2` (honest here because the
  ambient vertex type carries `[Fintype V]`).

## Published vs. arXiv v1

* **15.5** — the arXiv draft binds `Q` (*"let `Q ⊆ V(G) \ V(C)` be anticonnected"*) and then
  speaks of *"`X`-complete"*; the published version binds `X`, which is the correct reading and
  is the one transcribed here.
* **15.1** — the statement is identical in both versions, but its *proof* changed completely:
  the draft derived it from a Section 4 theorem (*"if `G` is Berge and admits a skew partition,
  then either `G` admits a balanced skew partition, or one of `G, Ḡ` contains a long prism, a
  double diamond, or `L(K₃,₃ \ e)`"*) that **does not exist in the published Section 4**; the
  published version argues directly from 4.2, 2.1 and `G ∈ F₆`.  The statements below are the
  published ones as printed.
* No other statement of Section 15 differs mathematically between the two versions.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S15

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.SkewTools StrongPerfectGraphTheorem.Types.SkewTools.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **15.1** (printed p. 92)

PAPER: *"If `G ∈ F₆` admits a skew partition, then `G` admits a balanced skew partition."*

Together with 1.5 (*"if `G` is a minimum imperfect graph, then `G` admits no balanced skew
partition"*) this is the paper's form of Chvátal's skew partition conjecture: no minimum
imperfect graph admits a skew partition. -/
theorem thm_15_1 (G : SimpleGraph V) (hG : InF6 G) (hskew : AdmitsSkewPartition G) :
    AdmitsBalancedSkewPartition G := by
  classical
  by_cases hloose : AdmitsLooseSkewPartition G
  · exact _root_.StrongPerfectGraphTheorem.Statements.S04.SPGT.thm_4_2 G hG.1.1.1 hloose
  · obtain ⟨A, B, hAB⟩ := hskew
    have hnl : ¬ IsLooseSkewPartition G A B := fun h => hloose ⟨A, B, h⟩
    refine ⟨A, B, hAB, ?_, ?_⟩
    · intro u v P hu hv hnadj hP hint hodd
      exact StrongPerfectGraphTheorem.ProofLemmas.Thm151Core.no_odd_path_of_not_loose hG hAB hnl hu hv hnadj hP hint hodd
    · intro u v Q hu hv hadj hQ hint hodd
      have hABc : IsSkewPartition Gᶜ B A := StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.isSkewPartition_compl.mpr hAB
      have hnlc : ¬ IsLooseSkewPartition Gᶜ B A := fun h =>
        hnl (StrongPerfectGraphTheorem.ProofLemmas.LooseSkewPartition.isLooseSkewPartition_of_compl h)
      have hGc : InF6 Gᶜ := StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.inF6_compl.mpr hG
      exact StrongPerfectGraphTheorem.ProofLemmas.Thm151Core.no_odd_path_of_not_loose hGc hABc hnlc hu hv
        (fun h => h.2 hadj) hQ hint hodd


end SPGT

end StrongPerfectGraphTheorem.Statements.S15
