module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Tracks
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.StripSystems
public import StrongPerfectGraphTheorem.Types.Overshadowed
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Statements.S08.Thm_8_1
public import StrongPerfectGraphTheorem.ProofLemmas.Thm82RungChoice
public import StrongPerfectGraphTheorem.ProofLemmas.Thm82BranchDelta

/-!
# Section 8 — Generalized line graphs

The six numbered statements 8.1–8.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 39–47).

All defined terms are imported and never restated: *`J`-strip system*, *`uv`-rung*,
*a choice of rungs forms `L(H)`*, *nondegenerate strip system*, *`V(S,N)`*, *saturates the
strip system*, *major* and *local* with respect to the strip system, *maximal strip system*
from `StrongPerfectGraphTheorem.Types.StripSystems`; *Berge*, *path*, *length*, *connected set* from
`StrongPerfectGraphTheorem.Types.Core`; *`k`-connected* from `StrongPerfectGraphTheorem.Types.Tracks`; *appearance*,
*(non)degenerate appearance*, *`J`-enlargement*, *saturates `L(H)`*, *attachments* from
`StrongPerfectGraphTheorem.Types.Appearances`; *overshadowed appearance* from `StrongPerfectGraphTheorem.Types.Overshadowed`;
*proper 2-join* and *balanced skew partition* from `StrongPerfectGraphTheorem.Types.Decompositions`.
-/

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S08

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Tracks StrongPerfectGraphTheorem.Types.Tracks.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.StripSystems StrongPerfectGraphTheorem.Types.StripSystems.SPGT
open StrongPerfectGraphTheorem.Types.Overshadowed StrongPerfectGraphTheorem.Types.Overshadowed.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **8.2** (printed p. 40)

PAPER: *"Let `(S,N)` be a `J`-strip system in a Berge graph `G`, where `J` is 3-connected.  If
there is an edge `uv` of `J` such that some `uv`-rung has length 0 and another `uv`-rung has
length `≥ 1`, then there is an overshadowed appearance of `J` in `G`."*

Notes on the transcription.

* *"Some `uv`-rung has length 0 and another `uv`-rung has length `≥ 1`"*: two `uv`-rungs `R`,
  `R'` with `pathLength R = 0` and `1 ≤ pathLength R'` (they are automatically different).
* *"There is an overshadowed appearance of `J` in `G`"*: there are a bipartite subdivision
  `H` of `J`, a vertex set `K'` of `G` and an identification `φ : H.lineGraph ≃g G.induce K'`
  making `L(H)` an appearance of `J` in `G` (`Appearances.IsAppearance`), which is
  overshadowed (`Overshadowed.IsOvershadowedAppearance`). -/
theorem thm_8_2 {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmixed : ∃ u v : U, J.Adj u v ∧ ∃ R R' : List V,
      IsUVRung G J S N u v R ∧ pathLength R = 0 ∧
      IsUVRung G J S N u v R' ∧ 1 ≤ pathLength R') :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' φ := by
  -- PAPER: the hypothesis names the edge `uv`, a `uv`-rung `R₀` of length `0` and a `uv`-rung
  -- `R₁` of length `≥ 1`.
  obtain ⟨u, v, huv, R₀, R₁, hR₀, hR₀len, hR₁, hR₁len⟩ := hmixed
  -- PAPER: *"Let `y` be the vertex of some `uv`-rung of length 0."*  A rung of length `0` is a
  -- one-vertex path, and its unique vertex `s` lies in `N_u ∩ N_v ∩ S_{uv}`.
  obtain ⟨-, s, t, hpf, hSsub, hNu, hNv⟩ := id hR₀
  have hne : R₀ ≠ [] := hpf.1.1
  have hst : s = t := by
    have h1 := hpf.2.1
    have h2 := hpf.2.2
    rcases R₀ with _ | ⟨a, l⟩
    · exact absurd rfl hne
    · have hl : l = [] := by
        have hl0 : l.length = 0 := by simpa [pathLength] using hR₀len
        simpa using hl0
      subst hl
      have h3 : some s = some t := by rw [← h1, ← h2]; simp
      simpa using h3
  have hsR : s ∈ R₀ := List.mem_of_mem_head? (by rw [hpf.2.1]; rfl)
  have hyS : s ∈ S u v := hSsub s hsR
  have hyNu : s ∈ N u := (hNu s hsR).mpr rfl
  have hyNv : s ∈ N v := (hNv s hsR).mpr hst
  -- PAPER: *"By 8.1, `R_uv` has even length."*  The rung `R₀` has length `0`, which is even.
  have hev : Even (pathLength R₁) :=
    (thm_8_1 G hG J hJ S N hSN u v huv R₀ R₁ hR₀ hR₁).mp (by rw [hR₀len]; exact ⟨0, rfl⟩)
  -- PAPER: *"For each edge `ij` of `J` choose an `ij`-rung `R_ij`, arbitrarily for every edge of
  -- `J` different from `uv`, and such that `R_uv` has length `≥ 1`; and let this choice of rungs
  -- form `L(H)`."*
  obtain ⟨n, H, R, hForms, hRuv⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm82RungChoice.thm82RungChoice G hG J hJ S N hSN u v huv R₁ hR₁
  -- PAPER: *"Let `B` be the branch of `H` between `u` and `v`, so `E(B) = V(R_uv)`."*
  obtain ⟨φ, B, b₁, b₂, hB, hBends, hBlen, hd1, hd2, hsub1, hsub2⟩ :=
    StrongPerfectGraphTheorem.ProofLemmas.Thm82BranchDelta.thm82BranchDelta G J hJ S N hSN H R hForms u v huv
  have hlenR : pathLength (R u v) = pathLength R₁ := by rw [hRuv]
  -- PAPER: *"Then `B` is odd and has length `≥ 3`"*.
  have hodd : Odd (trackLength B) := by
    rw [hBlen, hlenR]; exact hev.add_one
  have hge3 : 3 ≤ trackLength B := by
    obtain ⟨k, hk⟩ := hev
    rw [hBlen, hlenR]
    omega
  -- PAPER: *"and `y` is nonadjacent in `G` to at most one vertex of `G` in `δ_H(u)` and at most
  -- one in `δ_H(v)`.  Hence `L(H)` is overshadowed."*
  refine ⟨n, H, _, φ, hForms.2, B, b₁, b₂, hB, hBends, hodd, hge3, s, ?_, ?_⟩
  · -- at `δ_H(u)`: every edge of `δ_H(u)` whose vertex of `G` lies outside the strip `S_{uv}`
    -- lies in `N_u ∩ S_{uw}` for some `w ≠ v`, hence is adjacent to `y ∈ N_u ∩ S_{uv}` by the
    -- fifth axiom of a strip system; and at most one edge of `δ_H(u)` lands inside `S_{uv}`.
    refine Set.Subsingleton.anti hsub1 ?_
    rintro e ⟨heδ, hnadj⟩
    refine ⟨heδ, ?_⟩
    intro hE
    by_contra hnot
    have hx : (↑(φ ⟨e, hE⟩) : V) ∈ N u := hd1 e heδ hE
    have hmem := hSN.2.2.1 u hx
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨w, hw, hxw⟩ := hmem
    have hwv : v ≠ w := fun h => hnot (by rw [h]; exact hxw)
    have hadj := (hSN.2.2.2.2.2.1 u v w huv hw hwv).1 s ⟨hyNu, hyS⟩ _ ⟨hx, hxw⟩
    exact hnadj ⟨hE, hadj⟩
  · -- at `δ_H(v)`: the same argument with `u` and `v` interchanged, using `S_{vu} = S_{uv}`.
    refine Set.Subsingleton.anti hsub2 ?_
    rintro e ⟨heδ, hnadj⟩
    refine ⟨heδ, ?_⟩
    intro hE
    by_contra hnot
    have hx : (↑(φ ⟨e, hE⟩) : V) ∈ N v := hd2 e heδ hE
    have hmem := hSN.2.2.1 v hx
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨w, hw, hxw⟩ := hmem
    have hSvu : S v u = S u v := hSN.1 v u huv.symm
    have hwu : u ≠ w := fun h => hnot (by rw [← hSvu, h]; exact hxw)
    have hadj :=
      (hSN.2.2.2.2.2.1 v u w huv.symm hw hwu).1 s ⟨hyNv, by rw [hSvu]; exact hyS⟩ _ ⟨hx, hxw⟩
    exact hnadj ⟨hE, hadj⟩


end SPGT

end StrongPerfectGraphTheorem.Statements.S08
