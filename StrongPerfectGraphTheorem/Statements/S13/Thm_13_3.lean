/-  One numbered statement of the paper per module.  The module docstring below describes the
    whole of Section 13. -/

module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Staircases
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.ProofLemmas.PathBasics
public import StrongPerfectGraphTheorem.ProofLemmas.HoleBasics
public import StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas
public import StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm133Claim1
public import StrongPerfectGraphTheorem.ProofLemmas.Thm133SkewSetup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm133EvenPath
public import StrongPerfectGraphTheorem.ProofLemmas.Thm133EvenAntipath
public import StrongPerfectGraphTheorem.Statements.S04.Thm_4_6

/-!
# Section 13 — The long odd prism

The seven numbered statements 13.1–13.7 of Chudnovsky–Robertson–Seymour–Thomas, *The Strong
Perfect Graph Theorem* (published/Annals version, printed pages 78–86).

Every defined term used here is imported and never restated:

* *right-sequence*, *earlier*, *predecessor*, *trajectory*, *birth*, *`b`-optimal banister*,
  *3-breaker* and *recalcitrant* come from `StrongPerfectGraphTheorem.Types.LongOddPrism`;
* *strongly maximal staircase*, *right-star*, *banister*, *1-breaker* and *2-breaker* from
  `StrongPerfectGraphTheorem.Types.Staircases`;
* *even prism*, *long prism*, *odd prism* from `StrongPerfectGraphTheorem.Types.Prisms`;
* *appearance* from `StrongPerfectGraphTheorem.Types.Appearances`;
* the class `F₅` from `StrongPerfectGraphTheorem.Types.Classes`;
* *proper 2-join*, *proper homogeneous pair*, *balanced skew partition* from
  `StrongPerfectGraphTheorem.Types.Decompositions`;
* *Berge*, *path*, *antipath*, *length*, *interior*, *`X`-complete*, *`X`-complete edge*,
  *complete to*, *anticonnected* from `StrongPerfectGraphTheorem.Types.Core`.

Encoding conventions:

* a path/antipath is the list of its vertices in order; `V(P)` for such a list `P` is
  `{v | v ∈ P}`, `P*` is `SPGT.interior P` and the length of `P` is `pathLength P`;
* a staircase `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` is carried by the seven pieces of data
  `A C B : Set V`, `a₀ : V`, `R₀ : List V`, `b₀ : V`, and `V(K)` is `staircaseVertices`;
* the paper's right-sequence `x₁, …, x_t` is the list `x : List V`, and the set
  `X = {x₁, …, x_t}` is `{v | v ∈ x}`;
* *"there is no appearance of `K₄` in `G`"* is `¬ Appears G (⊤ : SimpleGraph (Fin 4))`;
* *"there is no even prism in `G`"* is: no three paths of `G` form an even prism;
* *"there is no 1-breaker in `G`"*, *"no 2-breaker"*, *"there is a 3-breaker"* existentially
  quantify the data carried by `IsOneBreaker`, `IsTwoBreaker`, `IsThreeBreaker`.

Published-vs-draft notes (see the transcription file for the full list):

* **13.4** is the *published* form: its 2-joins are **proper** 2-joins and its third outcome is
  *"`G` admits a **proper homogeneous pair**"* (the arXiv draft said *"an M-join"*).  Its
  hypothesis is transcribed literally — *"`G` is Berge, there is no appearance of `K₄` in
  either `G` or `Ḡ`, and `G` contains a long odd prism as an induced subgraph"* — and **not**
  as *"`G, Ḡ ∈ F₄`"*, which is how the statement 1.8.5 that 13.4 restates is phrased; the two
  agree only modulo the elsewhere-proved disposal of long *even* prisms.
* **13.6** carries the published hypothesis `X ⊆ V(G) \ V(P)` (the draft had `X ⊆ V(G)`).
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S13

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms StrongPerfectGraphTheorem.Types.Prisms.SPGT
open StrongPerfectGraphTheorem.Types.Staircases StrongPerfectGraphTheorem.Types.Staircases.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **13.3** (printed p. 83)

PAPER: *"Let `G` be Berge, containing no appearance of `K₄`, no even prism, no 1-breaker and
no 2-breaker.  Suppose that there is a 3-breaker in `G`; then `G` admits a balanced skew
partition."*

A 3-breaker is a pair `(K, x)` with `K = (S = (A, C, B), a₀`-`R₀`-`b₀)`, so *"there is a
3-breaker in `G`"* existentially quantifies the six pieces of staircase data together with the
vertex `x`. -/
theorem thm_13_3 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    (h3br : ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ x : V),
      IsThreeBreaker G A C B a₀ R₀ b₀ x) :
    AdmitsBalancedSkewPartition G := by
  classical
  obtain ⟨A, C, B, a₀, R₀, b₀, x₁, hbreaker⟩ := h3br
  have hsingle : IsRightSequence G A C B [x₁] := by
    refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
    · intro z hz
      have hzx : z = x₁ := by simpa using hz
      exact hzx ▸ hbreaker.2.2.1
    · intro i hi hcomp
      have hi0 : i = 0 := by simpa using hi
      subst i
      exact False.elim (hbreaker.2.2.2.1 (by simpa using hcomp))
    · intro i hi hanti
      have hi0 : i = 0 := by simpa using hi
      subst i
      exact False.elim (hbreaker.2.2.2.2 (by simpa using hanti))
  obtain ⟨x, hx, hxlen, hxmax⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.exists_max_rightSequence hsingle
  have hxne : x ≠ [] := by
    intro he
    rw [he] at hxlen
    simp at hxlen
  let c : StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ctx G A C B a₀ b₀ R₀ x :=
    { berge := hG
      noK4 := hK4
      noPrism := heven
      no1br := h1br
      no2br := h2br
      strongMax := hbreaker.1
      rseq := hx
      maximal := hxmax
      nonempty := hxne }
  by_cases hno : ¬ AdmitsBalancedSkewPartition G
  · have hclaim : ∀ (u : V) (P : List V), u ∈ A ∪ C → IsPathFrom G P u b₀ →
        ∃ w ∈ SPGT.interior P,
          w ∈ StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ws G A C B x := by
      intro u P hu hP
      exact StrongPerfectGraphTheorem.ProofLemmas.Thm133Claim1.thm133_claim1 c hu hP
    obtain ⟨A₁, hskewc, hkernel, hA₁, hA₁sub⟩ :=
      StrongPerfectGraphTheorem.ProofLemmas.Thm133SkewSetup.thm133_skew_setup c hclaim
    have hskew : IsSkewPartition G
        (StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ws G A C B x)ᶜ
        (StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ws G A C B x) :=
      StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.isSkewPartition_compl.mp hskewc
    have hcompResult : AdmitsBalancedSkewPartition Gᶜ :=
      _root_.StrongPerfectGraphTheorem.Statements.S04.SPGT.thm_4_6 Gᶜ
        (StrongPerfectGraphTheorem.ProofLemmas.HoleBasics.berge_compl.mpr hG)
        (StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ws G A C B x)
        (StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ws G A C B x)ᶜ (A ∪ C) A₁
        hskewc hkernel hA₁
        (by
          intro u hu v hv huv _ _
          by_cases huvEq : u = v
          · subst v
            refine ⟨[u], ⟨StrongPerfectGraphTheorem.ProofLemmas.PathBasics.isPathList_singleton Gᶜ u,
              by simp, by simp⟩,
              ?_, ⟨0, by rfl⟩⟩
            simp [SPGT.interior]
          · have huvG : G.Adj u v := by
              by_contra hn
              exact huv ((G.compl_adj u v).mpr ⟨huvEq, hn⟩)
            obtain ⟨q, hq, hqint, hqeven⟩ :=
              StrongPerfectGraphTheorem.ProofLemmas.Thm133EvenAntipath.thm133_even_antipath
                c hskew hno hu hv huvG
            exact ⟨q, hq, hqint, hqeven⟩)
        (by
          intro u hu v hv huv _ _
          have hu' : u ∈ StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ys G A C B x ∪ B :=
            hA₁sub hu
          have hv' : v ∈ StrongPerfectGraphTheorem.ProofLemmas.Thm133Setup.Ys G A C B x ∪ B :=
            hA₁sub hv
          obtain ⟨p, hp, hpint, hpeven⟩ :=
            StrongPerfectGraphTheorem.ProofLemmas.Thm133EvenPath.thm133_even_path c hu' hv' huv.2 huv.1
          refine ⟨p, ?_, ?_, hpeven⟩
          · change IsPathFrom (Gᶜ)ᶜ p u v
            simpa only [compl_compl] using hp
          · intro z hz
            exact c.AC_disjoint_W z (hpint z hz))
    exact StrongPerfectGraphTheorem.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp hcompResult
  · exact Classical.byContradiction hno


end SPGT

end StrongPerfectGraphTheorem.Statements.S13
