import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace standard05
def rows0 : List Row := [![1,0,⟨(-1),0⟩,0],![0,1,0,0],![0,0,0,1]]
theorem cover0 : Covers (standardProblem 5) rows0 := by
  exact covers_target (standardProblem 5) rows0 3 ![[],[],[],[],[],[],[],[(1,1)],[],[],[],[],[],[(2,1)],[],[]] (by decide +kernel)
def rows1 : List Row := [![0,1,0,0],![0,0,0,1]]
theorem cover1 : Covers (standardProblem 5) rows1 := by
  exact covers_target (standardProblem 5) rows1 3 ![[],[],[],[],[],[],[],[(0,1)],[],[],[],[],[],[(1,1)],[],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover2 : Covers (standardProblem 5) rows2 := by
  exact covers_target (standardProblem 5) rows2 0 ![[(0,1)],[],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[],[],[(3,1)],[],[]] (by decide +kernel)
def rows3 : List Row := [![1,0,0,0],![0,1,0,1],![0,0,1,0]]
theorem cover3 : Covers (standardProblem 5) rows3 := by
  exact covers_target (standardProblem 5) rows3 1 ![[(0,1)],[],[],[],[],[],[],[],[],[],[(2,1)],[],[],[],[],[]] (by decide +kernel)
def rows4 : List Row := [![1,0,⟨(-1),0⟩,0],![0,1,0,1]]
theorem cover4 : Covers (standardProblem 5) rows4 := by
  refine covers_split (standardProblem 5) rows4 4 ![rows0,rows2,rows3,rows2] ?_ ?_ ?_
  · exact Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,1)],[(0,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(-1/2),0⟩),(2,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover2) (Fin.cases (cover3) (Fin.cases (cover2) (fun i => Fin.elim0 i))))
def rows5 : List Row := [![0,1,0,1]]
theorem cover5 : Covers (standardProblem 5) rows5 := by
  refine covers_split (standardProblem 5) rows5 1 ![rows0,rows1,rows0,rows4] ?_ ?_ ?_
  · exact Fin.cases (![[(2,1)],[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(2,1)],[(0,⟨(1/2),0⟩),(4,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(4,⟨(-1/2),0⟩)]]) (Fin.cases (![[(2,1)],[(0,1)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover0) (Fin.cases (cover4) (fun i => Fin.elim0 i))))
def rows6 : List Row := [![1,0,1,0],![0,1,0,0],![0,0,0,1]]
theorem cover6 : Covers (standardProblem 5) rows6 := by
  exact covers_target (standardProblem 5) rows6 3 ![[],[],[],[],[],[],[],[(1,1)],[],[],[],[],[],[(2,1)],[],[]] (by decide +kernel)
def rows7 : List Row := [![1,0,1,0],![0,1,0,1]]
theorem cover7 : Covers (standardProblem 5) rows7 := by
  refine covers_split (standardProblem 5) rows7 1 ![rows2,rows6,rows2,rows3] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(5,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,1)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover2) (Fin.cases (cover6) (Fin.cases (cover2) (Fin.cases (cover3) (fun i => Fin.elim0 i))))
def rows8 : List Row := [![1,0,0,0],![0,1,0,⟨(-1),0⟩],![0,0,1,0]]
theorem cover8 : Covers (standardProblem 5) rows8 := by
  exact covers_target (standardProblem 5) rows8 1 ![[(0,1)],[],[],[],[],[],[],[],[],[],[(2,1)],[],[],[],[],[]] (by decide +kernel)
def rows9 : List Row := [![1,0,1,0],![0,1,0,⟨(-1),0⟩]]
theorem cover9 : Covers (standardProblem 5) rows9 := by
  refine covers_split (standardProblem 5) rows9 5 ![rows2,rows6,rows2,rows8] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(1,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,⟨(1/2),0⟩),(5,⟨(-1/2),0⟩)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)],[(1,⟨(-1/2),0⟩),(5,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨(1/2),0⟩)],[(1,1)],[(0,⟨(1/2),0⟩),(3,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover2) (Fin.cases (cover6) (Fin.cases (cover2) (Fin.cases (cover8) (fun i => Fin.elim0 i))))
def rows10 : List Row := [![1,0,0,0],![0,0,1,0]]
theorem cover10 : Covers (standardProblem 5) rows10 := by
  exact covers_target (standardProblem 5) rows10 1 ![[(0,1)],[],[],[],[],[],[],[],[],[],[(1,1)],[],[],[],[],[]] (by decide +kernel)
def rows11 : List Row := [![1,0,1,0]]
theorem cover11 : Covers (standardProblem 5) rows11 := by
  refine covers_split (standardProblem 5) rows11 1 ![rows8,rows9,rows8,rows10] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(4,1)],[(0,⟨(1/2),0⟩),(2,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,1)],[(4,1)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(4,1)],[(0,⟨(1/2),0⟩),(2,⟨(-1/2),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨(1/2),0⟩)],[(0,⟨(1/2),0⟩),(2,⟨(-1/2),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover8) (Fin.cases (cover9) (Fin.cases (cover8) (Fin.cases (cover10) (fun i => Fin.elim0 i))))
def rows12 : List Row := []
theorem cover12 : Covers (standardProblem 5) rows12 := by
  refine covers_split (standardProblem 5) rows12 0 ![rows5,rows7,rows11,rows7] ?_ ?_ ?_
  · exact Fin.cases (![[(2,⟨(-1),0⟩)]]) (Fin.cases (![[(0,1)],[(2,⟨(-1),0⟩)]]) (Fin.cases (![[(0,1)]]) (Fin.cases (![[(0,1)],[(2,⟨(-1),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover5) (Fin.cases (cover7) (Fin.cases (cover11) (Fin.cases (cover7) (fun i => Fin.elim0 i))))
theorem root : Covers (standardProblem 5) [] := cover12
end standard05
end Holant.Certificates.EqualityQuaternary.Klein.Finite
