module

public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.Prisms
public import StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathThirdTriangleVertexComplete
public import StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathOppositeTriangleCompleteAndEven
public import StrongPerfectGraphTheorem.ProofLemmas.GlobalMinimalPrismAntipathThm33Core
public import StrongPerfectGraphTheorem.Statements.S03.Thm_3_3

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.ProofLemmas

open StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.Prisms.SPGT

theorem GlobalMinimalPrismAntipathContradictsThm33
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (Y : Set V)
    (alpha beta : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V)
    (hprism : FormPrism G alpha beta (R 0) (R 1) (R 2))
    (hRoutside : ∀ i v, v ∈ R i → v ∉ Y)
    (hRlength : ∀ i, 1 < pathLength (R i))
    (hYmajor : ∀ y ∈ Y, MajorForPrism G alpha beta y)
    (hQ : Q = alpha 0 :: (q ++ [alpha 1]))
    (hQantipath : IsAntipathFrom G Q (alpha 0) (alpha 1))
    (hqY : ∀ x ∈ q, x ∈ Y)
    (halpha0 : ¬ VertexComplete G (alpha 0) Y)
    (halpha1 : ¬ VertexComplete G (alpha 1) Y)
    (hminimal : ∀ (u v : V) (S : List V),
      u ≠ v →
      ((u ∈ ({alpha 0, alpha 1, alpha 2} : Set V) ∧
          v ∈ ({alpha 0, alpha 1, alpha 2} : Set V)) ∨
        (u ∈ ({beta 0, beta 1, beta 2} : Set V) ∧
          v ∈ ({beta 0, beta 1, beta 2} : Set V))) →
      ¬ VertexComplete G u Y →
      ¬ VertexComplete G v Y →
      IsAntipathFrom G S u v →
      (∀ x ∈ interior S, x ∈ Y) →
      pathLength Q ≤ pathLength S) :
    False :=
  globalMinimalPrismAntipathContradictionCore G hG Y alpha beta R q Q
    hprism hRoutside hRlength hYmajor hQ hQantipath hqY halpha0 halpha1 hminimal

end StrongPerfectGraphTheorem.ProofLemmas
