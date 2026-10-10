import Holant.Certificates.TetrahedralDeck.FiniteData

/-! Exact integral encodings of twice the six proved bridge vectors. The216
triples are checked only after the six-point completeness theorem is proved. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant.Certificates.TwelveLoops Holant.Certificates.TetrahedralDeck

def gCandidate (i : Fin 6) (x : Word) : Gaussian :=
  ![gzero,gMatch 0 ((0 : Fin 4).castAdd 8) ((0 : Fin 4).castAdd 8) x,
    gMatch 1 ((0 : Fin 4).castAdd 8) ((0 : Fin 4).castAdd 8) x,
    gMatch 2 ((0 : Fin 4).castAdd 8) ((0 : Fin 4).castAdd 8) x,
    gneg (gMatch 2 ((1 : Fin 4).castAdd 8) ((1 : Fin 4).castAdd 8) x),
    gneg (gMatch 2 ((3 : Fin 4).castAdd 8) ((3 : Fin 4).castAdd 8) x)] i

def candidateCode (i : Fin 6) : Fin 16 → Gaussian := fun j => gCandidate i (words j)

def GoodTriple (t : Fin 3 → Fin 6) : Prop := ∀ j : Fin 16,
  gadd (candidateCode (t 0) j) (gadd (candidateCode (t 1) j) (candidateCode (t 2) j)) =
    gadd (candidateCode 1 j) (candidateCode 2 j)
instance (t : Fin 3 → Fin 6) : Decidable (GoodTriple t) := by unfold GoodTriple; infer_instance

def ordered : Fin 12 → Fin 3 → Fin 6 :=
  ![![0,1,2],![1,2,0],![2,0,1],![0,2,1],![1,0,2],![2,1,0],
    ![3,4,5],![4,5,3],![5,3,4],![3,5,4],![4,3,5],![5,4,3]]

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem candidateCode_injective : Function.Injective candidateCode := by decide
theorem ordered_injective : Function.Injective ordered := by decide

theorem goodTriple_iff_ordered : ∀ t : Fin 3 → Fin 6,
    GoodTriple t ↔ ∃ i : Fin 12, t = ordered i := by decide

theorem goodTriple_count : (Finset.univ.filter GoodTriple).card = 12 := by decide

theorem ordered_classes :
    (∀ i : Fin 6, List.Perm [ordered (i.castAdd 6) 0,ordered (i.castAdd 6) 1,ordered (i.castAdd 6) 2] [0,1,2]) ∧
    (∀ i : Fin 6, List.Perm [ordered (i.natAdd 6) 0,ordered (i.natAdd 6) 1,ordered (i.natAdd 6) 2] [3,4,5]) := by decide

end Holant.Certificates.TetrahedralBridge
