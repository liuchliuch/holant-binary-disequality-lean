import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard11
def rows0 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,0,1]]
theorem cover0 : Covers (standardProblem 11) rows0 := by
  exact covers_target (standardProblem 11) rows0 3 ![[],[(0,1)],[],[],[],[],[],[(1,1)],[],[],[],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows1 : List Row := [![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover1 : Covers (standardProblem 11) rows1 := by
  exact covers_target (standardProblem 11) rows1 2 ![[],[],[],[],[],[],[],[(0,1)],[],[],[(1,1)],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover2 : Covers (standardProblem 11) rows2 := by
  exact covers_target (standardProblem 11) rows2 1 ![[],[(0,1)],[],[],[],[],[],[],[],[],[(1,1)],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows3 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0]]
theorem cover3 : Covers (standardProblem 11) rows3 := by
  exact covers_target (standardProblem 11) rows3 0 ![[],[(0,1)],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[],[],[],[],[]] (by decide +kernel)
def rows4 : List Row := []
theorem cover4 : Covers (standardProblem 11) rows4 := by
  refine covers_split (standardProblem 11) rows4 0 ![rows0,rows1,rows2,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(1,1)],[(2,⟨(-1),0⟩)],[(3,⟨(-1),0⟩)]]) (Fin.cases (![[(2,⟨(-1),0⟩)],[(0,1)],[(3,⟨(-1),0⟩)]]) (Fin.cases (![[(1,1)],[(0,1)],[(3,⟨(-1),0⟩)]]) (Fin.cases (![[(1,1)],[(2,⟨(-1),0⟩)],[(0,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover2) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
theorem root : Covers (standardProblem 11) [] := cover4
end standard11
end Holant.Certificates.EqualityQuaternary.Klein.Finite
