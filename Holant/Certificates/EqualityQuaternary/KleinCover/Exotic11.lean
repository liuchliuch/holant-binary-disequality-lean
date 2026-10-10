import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace exotic11
def rows0 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,0,1]]
theorem cover0 : Covers (exoticProblem 11) rows0 := by
  exact covers_target (exoticProblem 11) rows0 1 ![[],[(0,1)],[],[],[],[],[],[(1,1)],[],[],[],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows1 : List Row := [![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover1 : Covers (exoticProblem 11) rows1 := by
  exact covers_target (exoticProblem 11) rows1 16 ![[],[],[],[],[],[],[],[(0,1)],[],[],[(1,1)],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0]]
theorem cover2 : Covers (exoticProblem 11) rows2 := by
  exact covers_target (exoticProblem 11) rows2 2 ![[],[(0,1)],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[],[],[],[],[]] (by decide +kernel)
def rows3 : List Row := [![1,0,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover3 : Covers (exoticProblem 11) rows3 := by
  exact covers_target (exoticProblem 11) rows3 11 ![[],[(0,1)],[],[],[],[],[],[],[],[],[(1,1)],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows4 : List Row := []
theorem cover4 : Covers (exoticProblem 11) rows4 := by
  refine covers_split (exoticProblem 11) rows4 4 ![rows0,rows1,rows2,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(1,1)],[(3,⟨0,(-1)⟩)],[(2,⟨(-1),0⟩)]]) (Fin.cases (![[(3,⟨0,(-1)⟩)],[(0,⟨(-1/2),0⟩)],[(2,⟨(-1),0⟩)]]) (Fin.cases (![[(1,1)],[(3,⟨0,(-1)⟩)],[(0,⟨(-1/2),0⟩)]]) (Fin.cases (![[(1,1)],[(0,⟨(-1/2),0⟩)],[(2,⟨(-1),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover2) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
theorem root : Covers (exoticProblem 11) [] := cover4
end exotic11
end Holant.Certificates.EqualityQuaternary.Klein.Finite
