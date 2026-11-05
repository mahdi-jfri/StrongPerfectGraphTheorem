module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Appearances
public import StrongPerfectGraphTheorem.Types.Pseudowheels
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.ProofLemmas.Thm186Setup
public import StrongPerfectGraphTheorem.ProofLemmas.Thm186Claim2
public import StrongPerfectGraphTheorem.ProofLemmas.Thm186Final

/-!
# 18.6 — assembly

The printed proof is a minimal-counterexample argument:

> *"Proof.  Suppose the theorem is false, and choose a minimal counterexample `F`.  From 18.5
> `|F| ≥ 2`.  (1) … (2) … Thus there is no such `F`.  This proves 18.6."*

so the assembly is exactly: negate the conclusion, take a minimal counterexample
(`Thm186Setup.exists_minCounterexample`), run claim (2) (`Thm186Claim2.claim2`, which itself
runs claim (1)), and hand both to the closing paragraph
(`Thm186Final.final_contradiction`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace StrongPerfectGraphTheorem.ProofLemmas.Thm186Assembly

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Appearances StrongPerfectGraphTheorem.Types.Appearances.SPGT
open StrongPerfectGraphTheorem.Types.Pseudowheels StrongPerfectGraphTheorem.Types.Pseudowheels.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **18.6**, in exactly the shape of
`StrongPerfectGraphTheorem.Statements.S18.SPGT.thm_18_6`. -/
theorem thm_18_6_full (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V) (P : List V)
    (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hF : ∀ f ∈ F, f ∉ X ∪ Y ∧ f ∉ P)
    (hFconn : ConnectedSet G F)
    (hFY : ∀ f ∈ F, ¬ VertexComplete G f Y) :
    ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
      (∀ w ∈ attachments G F {w : V | w ∈ P}, w ∈ q) ∧
      (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
      ((∃ f ∈ F, VertexComplete G f X) → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q)) := by
  -- *"Suppose the theorem is false, and choose a minimal counterexample `F`."*
  by_contra hcon
  obtain ⟨F₀, hmin⟩ :=
    Thm186Setup.exists_minCounterexample G X Y P p₁ pₙ F ⟨hF, hFconn, hFY⟩ hcon
  -- *"(2) There do not exist `a, b` … This proves (2)."*
  have h2 := Thm186Claim2.claim2 G hG X Y P p₁ pₙ hopt hhead hlast F₀ hmin
  -- *"Choose `b` … contrary to 2.3.  Thus there is no such `F`.  This proves 18.6."*
  exact Thm186Final.final_contradiction G hG X Y P p₁ pₙ hopt hhead hlast F₀ hmin h2

end StrongPerfectGraphTheorem.ProofLemmas.Thm186Assembly
