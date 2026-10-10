import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk00
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk01
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk02
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk03
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk04
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk05
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk06
import Holant.Pauli.ExoticKlein.SixPortAnchorBlocks.Chunk07

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option Elab.async false

def allAnchorBlockData : Fin 64 → FiniteTable AnchorWitness :=
  ![anchorBlockData00, anchorBlockData01, anchorBlockData02, anchorBlockData03, anchorBlockData04, anchorBlockData05, anchorBlockData06, anchorBlockData07, anchorBlockData08, anchorBlockData09, anchorBlockData10, anchorBlockData11, anchorBlockData12, anchorBlockData13, anchorBlockData14, anchorBlockData15, anchorBlockData16, anchorBlockData17, anchorBlockData18, anchorBlockData19, anchorBlockData20, anchorBlockData21, anchorBlockData22, anchorBlockData23, anchorBlockData24, anchorBlockData25, anchorBlockData26, anchorBlockData27, anchorBlockData28, anchorBlockData29, anchorBlockData30, anchorBlockData31, anchorBlockData32, anchorBlockData33, anchorBlockData34, anchorBlockData35, anchorBlockData36, anchorBlockData37, anchorBlockData38, anchorBlockData39, anchorBlockData40, anchorBlockData41, anchorBlockData42, anchorBlockData43, anchorBlockData44, anchorBlockData45, anchorBlockData46, anchorBlockData47, anchorBlockData48, anchorBlockData49, anchorBlockData50, anchorBlockData51, anchorBlockData52, anchorBlockData53, anchorBlockData54, anchorBlockData55, anchorBlockData56, anchorBlockData57, anchorBlockData58, anchorBlockData59, anchorBlockData60, anchorBlockData61, anchorBlockData62, anchorBlockData63]

theorem allAnchorBlocks_checked (b : Fin 64) : anchorBlockCheck b (allAnchorBlockData b) = true := by
  fin_cases b
  · exact anchorBlock00_checked
  · exact anchorBlock01_checked
  · exact anchorBlock02_checked
  · exact anchorBlock03_checked
  · exact anchorBlock04_checked
  · exact anchorBlock05_checked
  · exact anchorBlock06_checked
  · exact anchorBlock07_checked
  · exact anchorBlock08_checked
  · exact anchorBlock09_checked
  · exact anchorBlock10_checked
  · exact anchorBlock11_checked
  · exact anchorBlock12_checked
  · exact anchorBlock13_checked
  · exact anchorBlock14_checked
  · exact anchorBlock15_checked
  · exact anchorBlock16_checked
  · exact anchorBlock17_checked
  · exact anchorBlock18_checked
  · exact anchorBlock19_checked
  · exact anchorBlock20_checked
  · exact anchorBlock21_checked
  · exact anchorBlock22_checked
  · exact anchorBlock23_checked
  · exact anchorBlock24_checked
  · exact anchorBlock25_checked
  · exact anchorBlock26_checked
  · exact anchorBlock27_checked
  · exact anchorBlock28_checked
  · exact anchorBlock29_checked
  · exact anchorBlock30_checked
  · exact anchorBlock31_checked
  · exact anchorBlock32_checked
  · exact anchorBlock33_checked
  · exact anchorBlock34_checked
  · exact anchorBlock35_checked
  · exact anchorBlock36_checked
  · exact anchorBlock37_checked
  · exact anchorBlock38_checked
  · exact anchorBlock39_checked
  · exact anchorBlock40_checked
  · exact anchorBlock41_checked
  · exact anchorBlock42_checked
  · exact anchorBlock43_checked
  · exact anchorBlock44_checked
  · exact anchorBlock45_checked
  · exact anchorBlock46_checked
  · exact anchorBlock47_checked
  · exact anchorBlock48_checked
  · exact anchorBlock49_checked
  · exact anchorBlock50_checked
  · exact anchorBlock51_checked
  · exact anchorBlock52_checked
  · exact anchorBlock53_checked
  · exact anchorBlock54_checked
  · exact anchorBlock55_checked
  · exact anchorBlock56_checked
  · exact anchorBlock57_checked
  · exact anchorBlock58_checked
  · exact anchorBlock59_checked
  · exact anchorBlock60_checked
  · exact anchorBlock61_checked
  · exact anchorBlock62_checked
  · exact anchorBlock63_checked

/-- All 4,045 original representatives reduce by actual port/symmetry actions
to the listed 2,222 anchors. Minimal orbit cardinalities are not assumed. -/
theorem original_representatives_of_anchors
    (h : ∀ a, Solved (stateEquiv (representativeCode (anchorRepresentative a)))) :
    ∀ r, Solved (stateEquiv (representativeCode r)) :=
  all_representatives_of_anchors allAnchorBlockData allAnchorBlocks_checked h

end
end Holant.Pauli.ExoticKlein.SixPort
