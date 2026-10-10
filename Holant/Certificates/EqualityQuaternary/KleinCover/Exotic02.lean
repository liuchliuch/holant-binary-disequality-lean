import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace exotic02
def rows0 : List Row := [![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover0 : Covers (exoticProblem 2) rows0 := by
  exact covers_target (exoticProblem 2) rows0 21 ![[],[],[],[],[],[],[(0,1)],[],[],[(1,1)],[],[],[],[],[],[(2,1)]] (by decide +kernel)
def rows1 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0]]
theorem cover1 : Covers (exoticProblem 2) rows1 := by
  exact covers_target (exoticProblem 2) rows1 1 ![[(0,1)],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[],[],[],[],[],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,0,1]]
theorem cover2 : Covers (exoticProblem 2) rows2 := by
  exact covers_target (exoticProblem 2) rows2 2 ![[(0,1)],[],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[],[(2,1)]] (by decide +kernel)
def rows3 : List Row := [![1,0,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover3 : Covers (exoticProblem 2) rows3 := by
  exact covers_target (exoticProblem 2) rows3 6 ![[(0,1)],[],[],[],[],[],[],[],[],[(1,1)],[],[],[],[],[],[(2,1)]] (by decide +kernel)
def rows4 : List Row := []
theorem cover4 : Covers (exoticProblem 2) rows4 := by
  refine covers_split (exoticProblem 2) rows4 0 ![rows0,rows1,rows2,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(3,⟨0,1⟩)],[(2,⟨0,(-1)⟩)],[(1,⟨0,(1/2)⟩)]]) (Fin.cases (![[(0,1)],[(3,⟨0,1⟩)],[(2,⟨0,(-1)⟩)]]) (Fin.cases (![[(0,1)],[(3,⟨0,1⟩)],[(1,⟨0,(1/2)⟩)]]) (Fin.cases (![[(0,1)],[(2,⟨0,(-1)⟩)],[(1,⟨0,(1/2)⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover2) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
theorem root : Covers (exoticProblem 2) [] := cover4
end exotic02
end Holant.Certificates.EqualityQuaternary.Klein.Finite
