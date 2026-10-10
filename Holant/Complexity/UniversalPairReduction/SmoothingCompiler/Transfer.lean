import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ThreeQueryCount

/-! A semantic source equality changes only the correctness proof. The complete
finite machine, time polynomial and actual query bound are retained literally. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Computability
variable {A B C D : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
variable {ec : Encoding C Bool} {ed : Encoding D Bool} {f : A → B} {g : C → D}

def sourceTransfer (r : PolyTimeOracleReduction ea eb ec ed f g)
    (h : A → B) (heq : ∀x,h x=f x) : PolyTimeOracleReduction ea eb ec ed h g where
  machine := r.machine
  time := r.time
  correct oracle ho x := by
    rw [heq x]
    exact r.correct oracle ho x

theorem sourceTransfer_atMostQueries (r : PolyTimeOracleReduction ea eb ec ed f g)
    (h : A → B) (heq : ∀x,h x=f x) {count : ℕ}
    (hc : ThreeQuery.AtMostQueries r.machine count) :
    ThreeQuery.AtMostQueries (sourceTransfer r h heq).machine count := hc

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
