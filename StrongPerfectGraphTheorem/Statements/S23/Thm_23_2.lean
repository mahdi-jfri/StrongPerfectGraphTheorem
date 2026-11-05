module

public import Mathlib
public import StrongPerfectGraphTheorem.Types.Core
public import StrongPerfectGraphTheorem.Types.BasicClasses
public import StrongPerfectGraphTheorem.Types.Decompositions
public import StrongPerfectGraphTheorem.Types.SkewTools
public import StrongPerfectGraphTheorem.Types.Wheels
public import StrongPerfectGraphTheorem.Types.WheelSystems
public import StrongPerfectGraphTheorem.Types.Classes
public import StrongPerfectGraphTheorem.Types.LongOddPrism
public import StrongPerfectGraphTheorem.ProofLemmas.KiteTailBasics
public import StrongPerfectGraphTheorem.ProofLemmas.OptimalWheelChoice
public import StrongPerfectGraphTheorem.ProofLemmas.Thm232Configuration
public import StrongPerfectGraphTheorem.ProofLemmas.Thm232PathT
public import StrongPerfectGraphTheorem.ProofLemmas.Thm232NoDoubleNeighbour
public import StrongPerfectGraphTheorem.ProofLemmas.Thm232Endgame

@[expose] public section

set_option autoImplicit false

namespace StrongPerfectGraphTheorem.Statements.S23

open StrongPerfectGraphTheorem.Types.Core StrongPerfectGraphTheorem.Types.Core.SPGT
open StrongPerfectGraphTheorem.Types.BasicClasses StrongPerfectGraphTheorem.Types.BasicClasses.SPGT
open StrongPerfectGraphTheorem.Types.Decompositions StrongPerfectGraphTheorem.Types.Decompositions.SPGT
open StrongPerfectGraphTheorem.Types.SkewTools StrongPerfectGraphTheorem.Types.SkewTools.SPGT
open StrongPerfectGraphTheorem.Types.Wheels StrongPerfectGraphTheorem.Types.Wheels.SPGT
open StrongPerfectGraphTheorem.Types.WheelSystems StrongPerfectGraphTheorem.Types.WheelSystems.SPGT
open StrongPerfectGraphTheorem.Types.Classes StrongPerfectGraphTheorem.Types.Classes.SPGT
open StrongPerfectGraphTheorem.Types.LongOddPrism StrongPerfectGraphTheorem.Types.LongOddPrism.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem thm_23_2 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G) :
    ¬ ∃ (C : List V) (Y : Set V), IsWheel G C Y := by
  intro hex
  -- "Suppose there is a wheel in `G`, and choose an optimal wheel `(C,Y)` such that `C`
  -- contains as few `Y`-complete edges as possible."
  obtain ⟨C, Y, hopt, hmin⟩ :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.OptimalWheelChoice.exists_optimal_wheel G hex
  -- (1) and the configuration `x₀, z, x₁, c₁, c₂, c₃`.
  obtain ⟨x₀, z, x₁, c₁, c₂, c₃, k, d, hd2, hdn, hpre1, hpre2,
    ⟨hx₀C, hzC, hx₁C, hc₁C, hc₂C, hc₃C⟩,
    ⟨h0Y, hzY, h1Y, hc1Y, hc2Y, hc3Y⟩, hnb, hnbc, hxc, hcx, hdist, hedge, hexh⟩ :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.Thm232Configuration.exists_configuration G hG hbsp C Y hopt
      hmin
  -- "Since `G` does not admit a skew partition, there is a path `T` of `G \ {x₀,x₁}` from `z`
  -- to `A₀` … Let `y` be the neighbour of `z` in `T`."
  obtain ⟨T, R, y, w, hTeq, hpath, hwC, hwz, hw0, hw1, havoid, hint⟩ :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.Thm232PathT.exists_clean_path G hG hbsp C Y hopt hmin
      z x₀ x₁ hzC hnb h0Y hzY h1Y
  -- (2) "`y` is not adjacent to both `x₀`, `x₁`."
  have h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁) :=
    _root_.StrongPerfectGraphTheorem.ProofLemmas.Thm232NoDoubleNeighbour.not_adj_both G hG hbsp C Y hopt
      z x₀ x₁ y T R hzC hnb h0Y hzY h1Y hedge hTeq havoid ⟨w, hpath, hwC, hwz, hw0, hw1⟩ hint
  -- (3), (4), (5) and the closing paragraph.
  exact _root_.StrongPerfectGraphTheorem.ProofLemmas.Thm232Endgame.no_wheel_contradiction G hG hbsp C Y hopt
    hmin x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh
    T R y w hTeq hpath hwC hwz hw0 hw1 havoid hint h2


end SPGT

end StrongPerfectGraphTheorem.Statements.S23
