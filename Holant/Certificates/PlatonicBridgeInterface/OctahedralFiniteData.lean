import Holant.Certificates.PlatonicBridgeInterface.OctahedralTensorCode

/-! Literal kernel-checked tensor values and all four source frames. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant.Certificates.IcosahedralSeparator (GScalar gadd)
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def permutation : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],![1,2,0],![2,0,1],![0,2,1],![1,0,2],![2,1,0]]
def frames : Fin 4 → Fin 3 → Fin 9 := ![![0,1,2],![0,7,8],![1,5,6],![2,3,4]]
def ordering (i : Fin 24) (j : Fin 3) : Fin 9 :=
  frames ⟨i.val/6,by omega⟩ (permutation ⟨i.val%6,by omega⟩ j)

def candidateTable : Fin 12 → Fin 16 → GScalar :=
  ![![(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩)],
    ![(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩)],
    ![(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩)],
    ![(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩)],
    ![(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩)],
    ![(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨-4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨-4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩)],
    ![(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨2,0⟩,⟨0,0⟩)],
    ![(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨2,0⟩),(⟨0,0⟩,⟨-2,0⟩),(⟨2,0⟩,⟨0,0⟩)],
    ![(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨4,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-4,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩)],
    ![(⟨4,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨-4,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨4,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨0,0⟩,⟨0,0⟩),(⟨4,0⟩,⟨0,0⟩)],
    ![(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩)],
    ![(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨-2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩),(⟨2,0⟩,⟨0,0⟩)]]

theorem candidateTable_correct : ∀ i : Fin 12, ∀ w : Fin 16,
    candidateTable i w = candidateCode i (Holant.Certificates.TetrahedralDeck.words w) := by decide +kernel

def ordered (i : Fin 30) (j : Fin 3) : Fin 12 :=
  Fin.addCases (fun k : Fin 6 => (permutation k j).castAdd 9)
    (fun k : Fin 24 => (ordering k j).natAdd 3) i

def GoodTriple (t : Fin 3 → Fin 12) : Prop := ∀ w : Fin 16,
  gadd (gadd (candidateTable (t 0) w) (candidateTable (t 1) w)) (candidateTable (t 2) w) =
    gadd (candidateTable 1 w) (candidateTable 2 w)
instance (t : Fin 3 → Fin 12) : Decidable (GoodTriple t) := by unfold GoodTriple; infer_instance

theorem ordered_injective : Function.Injective ordered := by decide +kernel

theorem ordered_valid : ∀ i : Fin 30, GoodTriple (ordered i) := by decide +kernel

theorem goodTriple_first_0 : ∀ b c : Fin 12,
    GoodTriple ![0,b,c] ↔ ∃ k : Fin 30, ![0,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_1 : ∀ b c : Fin 12,
    GoodTriple ![1,b,c] ↔ ∃ k : Fin 30, ![1,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_2 : ∀ b c : Fin 12,
    GoodTriple ![2,b,c] ↔ ∃ k : Fin 30, ![2,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_3 : ∀ b c : Fin 12,
    GoodTriple ![3,b,c] ↔ ∃ k : Fin 30, ![3,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_4 : ∀ b c : Fin 12,
    GoodTriple ![4,b,c] ↔ ∃ k : Fin 30, ![4,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_5 : ∀ b c : Fin 12,
    GoodTriple ![5,b,c] ↔ ∃ k : Fin 30, ![5,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_6 : ∀ b c : Fin 12,
    GoodTriple ![6,b,c] ↔ ∃ k : Fin 30, ![6,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_7 : ∀ b c : Fin 12,
    GoodTriple ![7,b,c] ↔ ∃ k : Fin 30, ![7,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_8 : ∀ b c : Fin 12,
    GoodTriple ![8,b,c] ↔ ∃ k : Fin 30, ![8,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_9 : ∀ b c : Fin 12,
    GoodTriple ![9,b,c] ↔ ∃ k : Fin 30, ![9,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_10 : ∀ b c : Fin 12,
    GoodTriple ![10,b,c] ↔ ∃ k : Fin 30, ![10,b,c] = ordered k := by decide +kernel

theorem goodTriple_first_11 : ∀ b c : Fin 12,
    GoodTriple ![11,b,c] ↔ ∃ k : Fin 30, ![11,b,c] = ordered k := by decide +kernel

end Holant.Certificates.PlatonicBridgeInterface.Octahedral
