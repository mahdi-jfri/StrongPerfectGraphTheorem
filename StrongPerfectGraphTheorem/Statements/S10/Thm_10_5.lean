module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Statements.S07.Thm_7_3
public import StrongPerfectGraphTheorem.ProofLemmas.HyperprismFromPrism
public import StrongPerfectGraphTheorem.ProofLemmas.PrismSymmetry
public import StrongPerfectGraphTheorem.ProofLemmas.Thm105Endgame
public import StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup

/-!
# Section 10 — The even prism

The six numbered statements 10.1–10.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 56–63).

All the defined terms used here are imported and never restated: *prism* / *form a prism*,
*even prism*, *saturates*, *major*, *local* (with respect to a prism) come from
`StrongPerfectGraphTheorem.Types.Prisms`; *attachment* / *appearance* / *(non)degenerate appearance* from
`StrongPerfectGraphTheorem.Types.Appearances`; *Berge*, *connected set*, *path*, *length*, *interior* from
`StrongPerfectGraphTheorem.Types.Core`; *proper 2-join* and *balanced skew partition* from
`StrongPerfectGraphTheorem.Types.Decompositions`.

Encoding conventions:

* the paper's indices `1,2,3` are `0,1,2 : Fin 3`, so `R₁,R₂,R₃` is a family
  `R : Fin 3 → List V` and `a₁,a₂,a₃` is `a : Fin 3 → V` (this matches `Prisms`);
* a path is the list of its vertices in order, and `V(P)` for such a list `P` is
  `{v | v ∈ P}`; "a path in `F`" is a path of `G` all of whose vertices lie in `F`;
* `K` is the vertex set of the prism, i.e. `V(R₁) ∪ V(R₂) ∪ V(R₃)`, and
  `F ⊆ V(G) \ V(K)` is `F ⊆ Kᶜ`;
* "there is a nondegenerate appearance of `K₄` in `G`" is spelled out at each use as
  `∃ n (H : SimpleGraph (Fin n)) (K' : Set V), IsAppearance G K₄ H K' ∧
   NondegenerateAppearance K₄ H`, where `K₄` is `(⊤ : SimpleGraph (Fin 4))`;
* "the only edges between `X` and `Y` are …" is rendered as: every edge between `X` and `Y`
  is one of the listed ones (the listed ones being asserted separately as conjuncts).
-/

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


/-- **10.5** (printed p. 59), introduced by *"The next result is a close relative of 7.5."*

PAPER: *"Let `G` be Berge, such that there is no nondegenerate appearance of `K₄` in `G`.  If
there is an even prism `K` in `G`, such that some vertex of `G` is major with respect to `K`,
then `G` admits a balanced skew partition."*

The even prism and the major vertex are named rather than existentially quantified, which is
the same statement. -/
theorem thm_10_5 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (a b : Fin 3 → V) (R₁ R₂ R₃ : List V) (v : V)
    (hprism : IsEvenPrism G a b R₁ R₂ R₃)
    (hv : MajorForPrism G a b v) :
    AdmitsBalancedSkewPartition G := by
  classical
  let R₀ : Fin 3 → List V := ![R₁, R₂, R₃]
  have hprism₀ : IsEvenPrism G a b (R₀ 0) (R₀ 1) (R₀ 2) := by
    simpa [R₀] using hprism
  obtain ⟨α, β, R, Y, hgood, hmin, hmax⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.exists_optimal_choice
      G a b R₀ v hprism₀ hv
  obtain ⟨hchosen, hYne, hYanti, hYmajor⟩ := hgood
  have hYoutside : ∀ i : Fin 3, ∀ x ∈ R i, x ∉ Y := by
    intro i x hxR hxY
    apply StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.major_not_mem_evenPrism
      G α β R hchosen x (hYmajor x hxY)
    fin_cases i
    exacts [Or.inl (Or.inl hxR), Or.inl (Or.inr hxR), Or.inr hxR]
  have hlength : ∀ i : Fin 3, 1 < pathLength (R i) := by
    intro i
    have hlist :=
      StrongPerfectGraphTheorem.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length hchosen.1 i
    have hpos : 1 ≤ pathLength (R i) := by
      simp only [pathLength]
      omega
    have heven : Even (pathLength (R i)) := by
      fin_cases i
      exacts [hchosen.2.1, hchosen.2.2.1, hchosen.2.2.2]
    obtain ⟨k, hk⟩ := heven
    omega
  have hsat : SaturatesPrism α β {x : V | VertexComplete G x Y} :=
    StrongPerfectGraphTheorem.Statements.S07.SPGT.thm_7_3 G hG Y hYanti α β
      (R 0) (R 1) (R 2) hchosen.1 (hYoutside 0) (hYoutside 1)
      (hYoutside 2) (hlength 0) (hlength 1) (hlength 2) hYmajor
  have hαpairs :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.two_members_of_saturated_triple
      α {x : V | VertexComplete G x Y} hsat.1
  have hβpairs :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.two_members_of_saturated_triple
      β {x : V | VertexComplete G x Y} hsat.2
  obtain ⟨i, hαi, hβi⟩ : ∃ i : Fin 3,
      VertexComplete G (α i) Y ∧ VertexComplete G (β i) Y := by
    rcases hαpairs with hα01 | hα02 | hα12 <;>
      rcases hβpairs with hβ01 | hβ02 | hβ12
    · exact ⟨0, hα01.1, hβ01.1⟩
    · exact ⟨0, hα01.1, hβ02.1⟩
    · exact ⟨1, hα01.2, hβ12.1⟩
    · exact ⟨0, hα02.1, hβ01.1⟩
    · exact ⟨0, hα02.1, hβ02.1⟩
    · exact ⟨2, hα02.2, hβ12.2⟩
    · exact ⟨1, hα12.1, hβ01.2⟩
    · exact ⟨2, hα12.2, hβ02.2⟩
    · exact ⟨1, hα12.1, hβ12.1⟩
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  let α' : Fin 3 → V := fun j ↦ α (σ j)
  let β' : Fin 3 → V := fun j ↦ β (σ j)
  let R' : Fin 3 → List V := fun j ↦ R (σ j)
  have hσ0 : σ 0 = i := by simp [σ]
  have heven : ∀ j : Fin 3, Even (pathLength (R j)) := by
    intro j
    fin_cases j
    exacts [hchosen.2.1, hchosen.2.2.1, hchosen.2.2.2]
  have hprism' : IsEvenPrism G α' β' (R' 0) (R' 1) (R' 2) := by
    refine ⟨?_, heven (σ 0), heven (σ 1), heven (σ 2)⟩
    exact StrongPerfectGraphTheorem.ProofLemmas.PrismSymmetry.formPrism_perm hchosen.1 σ
  have hYmajor' : ∀ y ∈ Y, MajorForPrism G α' β' y := by
    intro y hy
    exact (StrongPerfectGraphTheorem.ProofLemmas.PrismSymmetry.majorForPrism_perm σ).mpr
      (hYmajor y hy)
  have hmax' : ∀ Z : Set V, Y ⊆ Z → AnticonnectedSet G Z →
      (∀ z ∈ Z, MajorForPrism G α' β' z) → Z = Y := by
    intro Z hYZ hZanti hZmajor
    apply hmax Z hYZ hZanti
    intro z hz
    exact (StrongPerfectGraphTheorem.ProofLemmas.PrismSymmetry.majorForPrism_perm σ).mp
      (hZmajor z hz)
  have hmin' : ∀ (a' b' : Fin 3 → V) (Q : Fin 3 → List V) (Z : Set V),
      StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.GoodChoice G a' b' Q Z →
        StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.triangleCompleteCount G α' β' Y ≤
          StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.triangleCompleteCount G a' b' Z := by
    intro a' b' Q Z hgood'
    rw [show StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.triangleCompleteCount G α' β' Y =
        StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.triangleCompleteCount G α β Y by
      exact StrongPerfectGraphTheorem.ProofLemmas.Thm105Setup.triangleCompleteCount_perm G α β Y σ]
    exact hmin a' b' Q Z hgood'
  have hsat' : SaturatesPrism α' β' {x : V | VertexComplete G x Y} :=
    (StrongPerfectGraphTheorem.ProofLemmas.PrismSymmetry.saturatesPrism_perm σ).mpr hsat
  have hα0 : VertexComplete G (α' 0) Y := by
    change VertexComplete G (α (σ 0)) Y
    rwa [hσ0]
  have hβ0 : VertexComplete G (β' 0) Y := by
    change VertexComplete G (β (σ 0)) Y
    rwa [hσ0]
  exact StrongPerfectGraphTheorem.ProofLemmas.Thm105Endgame.endgame G hG hK4 α' β' R' Y
    hprism' hYne hYanti hYmajor' hmax' hmin' hsat' hα0 hβ0


end SPGT

end StrongPerfectGraphTheorem.Statements.S10
