import Holant.Certificates.OctahedralSeparator.Data

/-! Exact pre-evaluated entries of the original four marked root dictionaries.
Every table entry is checked against the unchanged matrix expression by the kernel.
This caches arithmetic only; it does not enumerate candidate maps or tensors. -/
set_option maxHeartbeats 1200000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
abbrev RawVector := Fin 4 → Scalar

def rawCoordinates (U : Mat) : RawVector :=
  ![(U false false+U true true)/2,
    -(imag/2)*(U false true+U true false),
    (U false true-U true false)/2,
    -(imag/2)*(U false false-U true true)]

def rawPoint : Form → Fin 24 → RawVector :=
  ![![![1,0,0,0],
      ![0,1,0,0],
      ![0,0,1,0],
      ![0,0,0,1],
      ![1,1,1,1],
      ![1,1,1,(coeff (-1) 0 0 0)],
      ![1,1,(coeff (-1) 0 0 0),1],
      ![1,1,(coeff (-1) 0 0 0),(coeff (-1) 0 0 0)],
      ![1,(coeff (-1) 0 0 0),1,1],
      ![1,(coeff (-1) 0 0 0),1,(coeff (-1) 0 0 0)],
      ![1,(coeff (-1) 0 0 0),(coeff (-1) 0 0 0),1],
      ![1,(coeff (-1) 0 0 0),(coeff (-1) 0 0 0),(coeff (-1) 0 0 0)],
      ![1,1,0,0],
      ![1,(coeff (-1) 0 0 0),0,0],
      ![1,0,1,0],
      ![1,0,(coeff (-1) 0 0 0),0],
      ![1,0,0,1],
      ![1,0,0,(coeff (-1) 0 0 0)],
      ![0,1,1,0],
      ![0,1,(coeff (-1) 0 0 0),0],
      ![0,1,0,1],
      ![0,1,0,(coeff (-1) 0 0 0)],
      ![0,0,1,1],
      ![0,0,1,(coeff (-1) 0 0 0)]],
    ![![1,0,0,0],
      ![0,(coeff 0 (1/2) 0 0),0,(coeff 0 (1/2) 0 0)],
      ![0,(coeff 0 (1/2) 0 0),0,(coeff 0 (-1/2) 0 0)],
      ![0,0,1,0],
      ![1,(coeff 0 1 0 0),1,0],
      ![1,(coeff 0 1 0 0),(coeff (-1) 0 0 0),0],
      ![1,0,1,(coeff 0 1 0 0)],
      ![1,0,(coeff (-1) 0 0 0),(coeff 0 1 0 0)],
      ![1,0,1,(coeff 0 (-1) 0 0)],
      ![1,0,(coeff (-1) 0 0 0),(coeff 0 (-1) 0 0)],
      ![1,(coeff 0 (-1) 0 0),1,0],
      ![1,(coeff 0 (-1) 0 0),(coeff (-1) 0 0 0),0],
      ![1,(coeff 0 (1/2) 0 0),0,(coeff 0 (1/2) 0 0)],
      ![1,(coeff 0 (-1/2) 0 0),0,(coeff 0 (-1/2) 0 0)],
      ![1,(coeff 0 (1/2) 0 0),0,(coeff 0 (-1/2) 0 0)],
      ![1,(coeff 0 (-1/2) 0 0),0,(coeff 0 (1/2) 0 0)],
      ![1,0,1,0],
      ![1,0,(coeff (-1) 0 0 0),0],
      ![0,(coeff 0 1 0 0),0,0],
      ![0,0,0,(coeff 0 1 0 0)],
      ![0,(coeff 0 (1/2) 0 0),1,(coeff 0 (1/2) 0 0)],
      ![0,(coeff 0 (1/2) 0 0),(coeff (-1) 0 0 0),(coeff 0 (1/2) 0 0)],
      ![0,(coeff 0 (1/2) 0 0),1,(coeff 0 (-1/2) 0 0)],
      ![0,(coeff 0 (1/2) 0 0),(coeff (-1) 0 0 0),(coeff 0 (-1/2) 0 0)]],
    ![![1,0,0,0],
      ![0,1,0,0],
      ![0,0,(coeff 0 (1/2) 0 0),(coeff 0 (-1/2) 0 0)],
      ![0,0,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0)],
      ![1,1,(coeff 0 1 0 0),0],
      ![1,1,0,(coeff 0 (-1) 0 0)],
      ![1,1,0,(coeff 0 1 0 0)],
      ![1,1,(coeff 0 (-1) 0 0),0],
      ![1,(coeff (-1) 0 0 0),(coeff 0 1 0 0),0],
      ![1,(coeff (-1) 0 0 0),0,(coeff 0 (-1) 0 0)],
      ![1,(coeff (-1) 0 0 0),0,(coeff 0 1 0 0)],
      ![1,(coeff (-1) 0 0 0),(coeff 0 (-1) 0 0),0],
      ![1,1,0,0],
      ![1,(coeff (-1) 0 0 0),0,0],
      ![1,0,(coeff 0 (1/2) 0 0),(coeff 0 (-1/2) 0 0)],
      ![1,0,(coeff 0 (-1/2) 0 0),(coeff 0 (1/2) 0 0)],
      ![1,0,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0)],
      ![1,0,(coeff 0 (-1/2) 0 0),(coeff 0 (-1/2) 0 0)],
      ![0,1,(coeff 0 (1/2) 0 0),(coeff 0 (-1/2) 0 0)],
      ![0,1,(coeff 0 (-1/2) 0 0),(coeff 0 (1/2) 0 0)],
      ![0,1,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0)],
      ![0,1,(coeff 0 (-1/2) 0 0),(coeff 0 (-1/2) 0 0)],
      ![0,0,(coeff 0 1 0 0),0],
      ![0,0,0,(coeff 0 (-1) 0 0)]],
    ![![1,0,0,0],
      ![0,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0),0],
      ![0,(coeff 0 (-1/2) 0 0),(coeff 0 (1/2) 0 0),0],
      ![0,0,0,1],
      ![1,0,(coeff 0 1 0 0),1],
      ![1,0,(coeff 0 1 0 0),(coeff (-1) 0 0 0)],
      ![1,(coeff 0 1 0 0),0,1],
      ![1,(coeff 0 1 0 0),0,(coeff (-1) 0 0 0)],
      ![1,(coeff 0 (-1) 0 0),0,1],
      ![1,(coeff 0 (-1) 0 0),0,(coeff (-1) 0 0 0)],
      ![1,0,(coeff 0 (-1) 0 0),1],
      ![1,0,(coeff 0 (-1) 0 0),(coeff (-1) 0 0 0)],
      ![1,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0),0],
      ![1,(coeff 0 (-1/2) 0 0),(coeff 0 (-1/2) 0 0),0],
      ![1,(coeff 0 (-1/2) 0 0),(coeff 0 (1/2) 0 0),0],
      ![1,(coeff 0 (1/2) 0 0),(coeff 0 (-1/2) 0 0),0],
      ![1,0,0,1],
      ![1,0,0,(coeff (-1) 0 0 0)],
      ![0,0,(coeff 0 1 0 0),0],
      ![0,(coeff 0 1 0 0),0,0],
      ![0,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0),1],
      ![0,(coeff 0 (1/2) 0 0),(coeff 0 (1/2) 0 0),(coeff (-1) 0 0 0)],
      ![0,(coeff 0 (-1/2) 0 0),(coeff 0 (1/2) 0 0),1],
      ![0,(coeff 0 (-1/2) 0 0),(coeff 0 (1/2) 0 0),(coeff (-1) 0 0 0)]]]

theorem rawPoint_exact_0 : ∀ i : Fin 24, rawPoint (0 : Form) i =
    rawCoordinates (theta (0 : Form) (standard i)) := by
  intro i
  fin_cases i <;> decide +kernel

theorem rawPoint_exact_1 : ∀ i : Fin 24, rawPoint (1 : Form) i =
    rawCoordinates (theta (1 : Form) (standard i)) := by
  intro i
  fin_cases i <;> decide +kernel

theorem rawPoint_exact_2 : ∀ i : Fin 24, rawPoint (2 : Form) i =
    rawCoordinates (theta (2 : Form) (standard i)) := by
  intro i
  fin_cases i <;> decide +kernel

theorem rawPoint_exact_3 : ∀ i : Fin 24, rawPoint (3 : Form) i =
    rawCoordinates (theta (3 : Form) (standard i)) := by
  intro i
  fin_cases i <;> decide +kernel

theorem rawPoint_exact (f : Form) (i : Fin 24) :
    rawPoint f i=rawCoordinates (theta f (standard i)) := by
  fin_cases f
  · exact rawPoint_exact_0 i
  · exact rawPoint_exact_1 i
  · exact rawPoint_exact_2 i
  · exact rawPoint_exact_3 i

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
