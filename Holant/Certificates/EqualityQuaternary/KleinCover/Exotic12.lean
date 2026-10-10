import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace exotic12
def rows0 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0]]
theorem cover0 : Covers (exoticProblem 12) rows0 := by
  exact covers_target (exoticProblem 12) rows0 1 ![[],[],[(0,1)],[],[(1,1)],[],[],[],[],[(2,1)],[],[],[],[],[],[]] (by decide +kernel)
def rows1 : List Row := [![1,0,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover1 : Covers (exoticProblem 12) rows1 := by
  exact covers_target (exoticProblem 12) rows1 16 ![[],[],[(0,1)],[],[],[],[],[],[],[(1,1)],[],[],[],[],[],[(2,1)]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,0,1]]
theorem cover2 : Covers (exoticProblem 12) rows2 := by
  exact covers_target (exoticProblem 12) rows2 2 ![[],[],[(0,1)],[],[(1,1)],[],[],[],[],[],[],[],[],[],[],[(2,1)]] (by decide +kernel)
def rows3 : List Row := [![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover3 : Covers (exoticProblem 12) rows3 := by
  exact covers_target (exoticProblem 12) rows3 11 ![[],[],[],[],[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[(2,1)]] (by decide +kernel)
def rows4 : List Row := []
theorem cover4 : Covers (exoticProblem 12) rows4 := by
  refine covers_split (exoticProblem 12) rows4 4 ![rows0,rows1,rows2,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(3,⟨(-1),0⟩)],[(1,1)],[(2,⟨0,(-1)⟩)]]) (Fin.cases (![[(3,⟨(-1),0⟩)],[(2,⟨0,(-1)⟩)],[(0,⟨(-1/2),0⟩)]]) (Fin.cases (![[(3,⟨(-1),0⟩)],[(1,1)],[(0,⟨(-1/2),0⟩)]]) (Fin.cases (![[(1,1)],[(2,⟨0,(-1)⟩)],[(0,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover2) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
theorem root : Covers (exoticProblem 12) [] := cover4
end exotic12
end Holant.Certificates.EqualityQuaternary.Klein.Finite
