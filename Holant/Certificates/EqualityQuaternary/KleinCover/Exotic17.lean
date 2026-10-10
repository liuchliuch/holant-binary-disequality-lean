import Holant.Certificates.EqualityQuaternary.KleinFiniteData

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Linear
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace exotic17
def rows0 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,⟨0,1⟩]]
theorem cover0 : Covers (exoticProblem 17) rows0 := by
  exact covers_target (exoticProblem 17) rows0 2 ![[],[],[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[]] (by decide +kernel)
def rows1 : List Row := [![1,⟨0,(-1)⟩,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover1 : Covers (exoticProblem 17) rows1 := by
  exact covers_target (exoticProblem 17) rows1 9 ![[],[],[],[],[],[],[],[(0,⟨0,1⟩)],[],[],[],[],[(1,⟨0,1⟩),(2,1)],[],[],[]] (by decide +kernel)
def rows2 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover2 : Covers (exoticProblem 17) rows2 := by
  exact covers_target (exoticProblem 17) rows2 0 ![[],[],[(0,1)],[],[],[],[],[(1,1)],[],[(2,1)],[],[],[(3,1)],[],[],[]] (by decide +kernel)
def rows3 : List Row := [![1,⟨0,(-1)⟩,0,0],![0,0,1,⟨0,1⟩]]
theorem cover3 : Covers (exoticProblem 17) rows3 := by
  refine covers_split (exoticProblem 17) rows3 6 ![rows0,rows1,rows2,rows2] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨0,(1/4)⟩)],[(0,⟨0,(1/2)⟩),(3,⟨(1/4),0⟩)],[(1,1)]]) (Fin.cases (![[(0,1)],[(1,⟨(1/2),0⟩),(2,⟨0,(-1/4)⟩)],[(1,⟨0,(-1/2)⟩),(2,⟨(1/4),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨0,(1/4)⟩)],[(0,⟨0,(1/2)⟩),(3,⟨(1/4),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨0,(-1/4)⟩)],[(1,⟨0,(-1/2)⟩),(2,⟨(1/4),0⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(3,⟨0,(1/4)⟩)],[(0,⟨0,(1/2)⟩),(3,⟨(1/4),0⟩)],[(1,⟨(1/2),0⟩),(2,⟨0,(-1/4)⟩)],[(1,⟨0,(-1/2)⟩),(2,⟨(1/4),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover0) (Fin.cases (cover1) (Fin.cases (cover2) (Fin.cases (cover2) (fun i => Fin.elim0 i))))
def rows4 : List Row := [![1,0,0,0],![0,1,0,0]]
theorem cover4 : Covers (exoticProblem 17) rows4 := by
  exact covers_target (exoticProblem 17) rows4 2 ![[],[],[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[]] (by decide +kernel)
def rows5 : List Row := [![1,⟨0,(-1)⟩,0,0],![0,0,1,⟨0,(-1)⟩]]
theorem cover5 : Covers (exoticProblem 17) rows5 := by
  exact covers_target (exoticProblem 17) rows5 9 ![[],[],[],[],[],[],[],[(0,⟨0,1⟩)],[],[],[],[],[(1,⟨0,1⟩)],[],[],[]] (by decide +kernel)
def rows6 : List Row := [![1,0,0,0],![0,1,0,0],![0,0,1,⟨0,(-1)⟩]]
theorem cover6 : Covers (exoticProblem 17) rows6 := by
  exact covers_target (exoticProblem 17) rows6 2 ![[],[],[(0,1)],[],[],[],[],[(1,1)],[],[],[],[],[],[],[],[]] (by decide +kernel)
def rows7 : List Row := [![1,⟨0,(-1)⟩,0,0]]
theorem cover7 : Covers (exoticProblem 17) rows7 := by
  refine covers_split (exoticProblem 17) rows7 6 ![rows4,rows5,rows6,rows6] ?_ ?_ ?_
  · exact Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨0,(1/4)⟩)],[(0,⟨0,(1/2)⟩),(2,⟨(1/4),0⟩)]]) (Fin.cases (![[(0,1)],[(1,⟨0,(-1/2)⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨0,(1/4)⟩)],[(0,⟨0,(1/2)⟩),(2,⟨(1/4),0⟩)],[(1,⟨0,(-1/2)⟩)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(2,⟨0,(1/4)⟩)],[(0,⟨0,(1/2)⟩),(2,⟨(1/4),0⟩)],[(1,⟨0,(-1/2)⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover4) (Fin.cases (cover5) (Fin.cases (cover6) (Fin.cases (cover6) (fun i => Fin.elim0 i))))
def rows8 : List Row := [![1,⟨0,1⟩,0,0],![0,0,1,⟨0,1⟩]]
theorem cover8 : Covers (exoticProblem 17) rows8 := by
  exact covers_target (exoticProblem 17) rows8 12 ![[],[],[],[],[],[],[],[(0,⟨0,(-1)⟩)],[],[],[],[],[(1,⟨0,(-1)⟩)],[],[],[]] (by decide +kernel)
def rows9 : List Row := [![0,0,1,0],![0,0,0,1]]
theorem cover9 : Covers (exoticProblem 17) rows9 := by
  exact covers_target (exoticProblem 17) rows9 11 ![[],[],[],[],[],[],[],[],[],[(0,1)],[],[],[(1,1)],[],[],[]] (by decide +kernel)
def rows10 : List Row := [![1,⟨0,1⟩,0,0],![0,0,1,0],![0,0,0,1]]
theorem cover10 : Covers (exoticProblem 17) rows10 := by
  exact covers_target (exoticProblem 17) rows10 11 ![[],[],[],[],[],[],[],[],[],[(1,1)],[],[],[(2,1)],[],[],[]] (by decide +kernel)
def rows11 : List Row := [![0,0,1,⟨0,1⟩]]
theorem cover11 : Covers (exoticProblem 17) rows11 := by
  refine covers_split (exoticProblem 17) rows11 6 ![rows8,rows9,rows10,rows10] ?_ ?_ ?_
  · exact Fin.cases (![[(2,⟨0,(1/2)⟩)],[(0,1)]]) (Fin.cases (![[(0,⟨(1/2),0⟩),(1,⟨0,(-1/4)⟩)],[(0,⟨0,(-1/2)⟩),(1,⟨(1/4),0⟩)]]) (Fin.cases (![[(2,⟨0,(1/2)⟩)],[(0,⟨(1/2),0⟩),(1,⟨0,(-1/4)⟩)],[(0,⟨0,(-1/2)⟩),(1,⟨(1/4),0⟩)]]) (Fin.cases (![[(2,⟨0,(1/2)⟩)],[(0,⟨(1/2),0⟩),(1,⟨0,(-1/4)⟩)],[(0,⟨0,(-1/2)⟩),(1,⟨(1/4),0⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover8) (Fin.cases (cover9) (Fin.cases (cover10) (Fin.cases (cover10) (fun i => Fin.elim0 i))))
def rows12 : List Row := []
theorem cover12 : Covers (exoticProblem 17) rows12 := by
  refine covers_split (exoticProblem 17) rows12 4 ![rows3,rows3,rows7,rows11] ?_ ?_ ?_
  · exact Fin.cases (![[(3,⟨(-1),0⟩)],[(2,⟨0,(-1)⟩)]]) (Fin.cases (![[(3,⟨(-1),0⟩)],[(2,⟨0,(-1)⟩)]]) (Fin.cases (![[(3,⟨(-1),0⟩)]]) (Fin.cases (![[(2,⟨0,(-1)⟩)]]) (fun i => Fin.elim0 i))))
  · intro a
    fin_cases a <;> decide +kernel
  · exact Fin.cases (cover3) (Fin.cases (cover3) (Fin.cases (cover7) (Fin.cases (cover11) (fun i => Fin.elim0 i))))
theorem root : Covers (exoticProblem 17) [] := cover12
end exotic17
end Holant.Certificates.EqualityQuaternary.Klein.Finite
