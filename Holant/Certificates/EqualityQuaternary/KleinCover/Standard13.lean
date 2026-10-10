import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard13
def rows0 : List Row := [![1,0,0,0],![0,1,1,0],![0,0,0,1]]
theorem cover0 : Covers (standardProblem 13) rows0 := by
  exact covers_target (standardProblem 13) rows0 2 ![[],[],[(0,1)],[],[],[],[],[],[],[],[],[],[],[(2,1)],[],[]] (by decide +kernel)
def rows1 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover1 : Covers (standardProblem 13) rows1 := by
  exact covers_target (standardProblem 13) rows1 0 ![[],[],[(0,1)],[],[(1,1)],[],[],[],[],[],[],[(2,1)],[],[(3,1)],[],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,⟨(-1),0⟩],![0,1,0,0],![0,0,1,0]]
theorem cover2 : Covers (standardProblem 13) rows2 := by
  exact covers_target (standardProblem 13) rows2 1 ![[],[],[],[],[(1,1)],[],[],[],[],[],[],[(2,1)],[],[],[],[]] (by decide +kernel)
def rows3 : List Row := [![1,0,0,⟨(-1),0⟩],![0,1,1,0]]
theorem cover3 : Covers (standardProblem 13) rows3 := by
  refine covers_split (standardProblem 13) rows3 1 ![rows0,rows1,rows1,rows2] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,1)],[(0,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(-1/2),0⟩)],[(0,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(-1/2),0⟩)],[(0,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover1) (Fin.cases (cover2) (fun i => Fin.elim0 i))))
def rows4 : List Row := [![1,0,0,0],![0,0,0,1]]
theorem cover4 : Covers (standardProblem 13) rows4 := by
  exact covers_target (standardProblem 13) rows4 2 ![[],[],[(0,1)],[],[],[],[],[],[],[],[],[],[],[(1,1)],[],[]] (by decide +kernel)
def rows5 : List Row := [![1,0,0,0],![0,1,⟨(-1),0⟩,0],![0,0,0,1]]
theorem cover5 : Covers (standardProblem 13) rows5 := by
  exact covers_target (standardProblem 13) rows5 2 ![[],[],[(0,1)],[],[],[],[],[],[],[],[],[],[],[(2,1)],[],[]] (by decide +kernel)
def rows6 : List Row := [![1,0,0,⟨(-1),0⟩],![0,1,⟨(-1),0⟩,0]]
theorem cover6 : Covers (standardProblem 13) rows6 := by
  refine covers_split (standardProblem 13) rows6 5 ![rows5,rows1,rows1,rows2] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,1)],[(0,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover5) (Fin.cases (cover1) (Fin.cases (cover1) (Fin.cases (cover2) (fun i => Fin.elim0 i))))
def rows7 : List Row := [![1,0,0,⟨(-1),0⟩]]
theorem cover7 : Covers (standardProblem 13) rows7 := by
  refine covers_split (standardProblem 13) rows7 1 ![rows4,rows5,rows5,rows6] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(0,⟨(-1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,1)],[(0,⟨(-1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)],[(1,1)],[(0,⟨(-1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover4) (Fin.cases (cover5) (Fin.cases (cover5) (Fin.cases (cover6) (fun i => Fin.elim0 i))))
def rows8 : List Row := [![1,0,0,1],![0,1,0,0],![0,0,1,0]]
theorem cover8 : Covers (standardProblem 13) rows8 := by
  exact covers_target (standardProblem 13) rows8 1 ![[],[],[],[],[(1,1)],[],[],[],[],[],[],[(2,1)],[],[],[],[]] (by decide +kernel)
def rows9 : List Row := [![1,0,0,1],![0,1,1,0]]
theorem cover9 : Covers (standardProblem 13) rows9 := by
  refine covers_split (standardProblem 13) rows9 4 ![rows1,rows0,rows8,rows1] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(1,1)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover1) (Fin.cases (cover0) (Fin.cases (cover8) (Fin.cases (cover1) (fun i => Fin.elim0 i))))
def rows10 : List Row := [![0,1,0,0],![0,0,1,0]]
theorem cover10 : Covers (standardProblem 13) rows10 := by
  exact covers_target (standardProblem 13) rows10 1 ![[],[],[],[],[(0,1)],[],[],[],[],[],[],[(1,1)],[],[],[],[]] (by decide +kernel)
def rows11 : List Row := [![0,1,1,0]]
theorem cover11 : Covers (standardProblem 13) rows11 := by
  refine covers_split (standardProblem 13) rows11 1 ![rows9,rows8,rows8,rows10] ?_ ?_ ?_
  · exact Fin.cases (![[(4,⟨(-1),0⟩)],[(0,1)]]) (Fin.cases (![[(4,⟨(-1),0⟩)],[(0,⟨(1/2),0⟩),(1,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(1,⟨(-1/2),0⟩)]]) (Fin.cases (![[(4,⟨(-1),0⟩)],[(0,⟨(1/2),0⟩),(1,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(1,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(1,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(1,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover9) (Fin.cases (cover8) (Fin.cases (cover8) (Fin.cases (cover10) (fun i => Fin.elim0 i))))
def rows12 : List Row := []
theorem cover12 : Covers (standardProblem 13) rows12 := by
  refine covers_split (standardProblem 13) rows12 0 ![rows3,rows7,rows11,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(2,1)],[(1,1)]]) (Fin.cases (![[(2,1)]]) (Fin.cases (![[(1,1)]]) (Fin.cases (![[(2,1)],[(1,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover3) (Fin.cases (cover7) (Fin.cases (cover11) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
theorem root : Covers (standardProblem 13) [] := cover12
end standard13
end Holant.Certificates.EqualityQuaternary.Klein.Finite
