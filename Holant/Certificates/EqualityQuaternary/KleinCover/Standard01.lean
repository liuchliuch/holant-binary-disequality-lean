import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard01
def rows0 : List Row := [![1,⟨(-1),0⟩,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover0 : Covers (standardProblem 1) rows0 := by
  exact covers_target (standardProblem 1) rows0 3 ![[],[],[],[],[],[],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[]] (by decide +kernel)
def rows1 : List Row := [![0,0,1,0],![0,0,0,1]]
theorem cover1 : Covers (standardProblem 1) rows1 := by
  exact covers_target (standardProblem 1) rows1 3 ![[],[],[],[],[],[],[],[],[],[],[],[(0,1)],[],[],[(1,1)],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,1]]
theorem cover2 : Covers (standardProblem 1) rows2 := by
  exact covers_target (standardProblem 1) rows2 2 ![[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[],[],[]] (by decide +kernel)
def rows3 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover3 : Covers (standardProblem 1) rows3 := by
  exact covers_target (standardProblem 1) rows3 0 ![[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[(2,1)],[],[],[(3,1)],[]] (by decide +kernel)
def rows4 : List Row := [![1,⟨(-1),0⟩,0,0],![0,0,1,1]]
theorem cover4 : Covers (standardProblem 1) rows4 := by
  refine covers_split (standardProblem 1) rows4 4 ![rows0,rows2,rows3,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,1)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover2) (Fin.cases (cover3) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
def rows5 : List Row := [![0,0,1,1]]
theorem cover5 : Covers (standardProblem 1) rows5 := by
  refine covers_split (standardProblem 1) rows5 2 ![rows0,rows0,rows1,rows4] ?_ ?_ ?_
  · exact Fin.cases (![[(3,1)],[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(3,1)],[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(3,1)],[(0,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover4) (fun i => Fin.elim0 i))))
def rows6 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,⟨(-1),0⟩]]
theorem cover6 : Covers (standardProblem 1) rows6 := by
  exact covers_target (standardProblem 1) rows6 2 ![[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[],[],[]] (by decide +kernel)
def rows7 : List Row := [![1,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover7 : Covers (standardProblem 1) rows7 := by
  exact covers_target (standardProblem 1) rows7 3 ![[],[],[],[],[],[],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[]] (by decide +kernel)
def rows8 : List Row := [![1,1,0,0],![0,0,1,⟨(-1),0⟩]]
theorem cover8 : Covers (standardProblem 1) rows8 := by
  refine covers_split (standardProblem 1) rows8 6 ![rows3,rows3,rows7,rows6] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover3) (Fin.cases (cover3) (Fin.cases (cover7) (Fin.cases (cover6) (fun i => Fin.elim0 i))))
def rows9 : List Row := [![1,0,0,0],![0,1,0,0]]
theorem cover9 : Covers (standardProblem 1) rows9 := by
  exact covers_target (standardProblem 1) rows9 2 ![[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[],[],[]] (by decide +kernel)
def rows10 : List Row := [![1,1,0,0]]
theorem cover10 : Covers (standardProblem 1) rows10 := by
  refine covers_split (standardProblem 1) rows10 2 ![rows6,rows6,rows8,rows9] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(4,1)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(4,1)]]) (Fin.cases (![[(0,1)],[(4,1)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover6) (Fin.cases (cover6) (Fin.cases (cover8) (Fin.cases (cover9) (fun i => Fin.elim0 i))))
def rows11 : List Row := [![1,1,0,0],![0,0,1,1]]
theorem cover11 : Covers (standardProblem 1) rows11 := by
  refine covers_split (standardProblem 1) rows11 2 ![rows3,rows3,rows7,rows2] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(5,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover3) (Fin.cases (cover3) (Fin.cases (cover7) (Fin.cases (cover2) (fun i => Fin.elim0 i))))
def rows12 : List Row := []
theorem cover12 : Covers (standardProblem 1) rows12 := by
  refine covers_split (standardProblem 1) rows12 0 ![rows5,rows10,rows11,rows11] ?_ ?_ ?_
  · exact Fin.cases (![[(1,1)]]) (Fin.cases (![[(0,1)]]) (Fin.cases (![[(0,1)],[(1,1)]]) (Fin.cases (![[(0,1)],[(1,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover5) (Fin.cases (cover10) (Fin.cases (cover11) (Fin.cases (cover11) (fun i => Fin.elim0 i))))
theorem root : Covers (standardProblem 1) [] := cover12
end standard01
end Holant.Certificates.EqualityQuaternary.Klein.Finite
