import Holant.Certificates.FourthRootOdd.FamilyBlocks0
import Holant.Certificates.FourthRootOdd.FamilyBlocks1
import Holant.Certificates.FourthRootOdd.FamilyBlocks2
import Holant.Certificates.FourthRootOdd.FamilyBlocks3
import Holant.Certificates.FourthRootOdd.FamilyBlocks4
import Holant.Certificates.FourthRootOdd.FamilyBlocks5
import Holant.Certificates.FourthRootOdd.FamilyBlocks6
import Holant.Certificates.FourthRootOdd.FamilyBlocks7
import Holant.Certificates.FourthRootOdd.FamilyShift

namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops

theorem phase_test_in_family (s : State) (h : phaseTest s 0) : s=familyState (recoverFamily s 0) := by
  rcases s with ⟨⟨i,j,k⟩,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact family_recover_000 b h
  · exact family_recover_001 b h
  · exact family_recover_002 b h
  · exact family_recover_003 b h
  · exact family_recover_010 b h
  · exact family_recover_011 b h
  · exact family_recover_012 b h
  · exact family_recover_013 b h
  · exact family_recover_020 b h
  · exact family_recover_021 b h
  · exact family_recover_022 b h
  · exact family_recover_023 b h
  · exact family_recover_030 b h
  · exact family_recover_031 b h
  · exact family_recover_032 b h
  · exact family_recover_033 b h
  · exact family_recover_100 b h
  · exact family_recover_101 b h
  · exact family_recover_102 b h
  · exact family_recover_103 b h
  · exact family_recover_110 b h
  · exact family_recover_111 b h
  · exact family_recover_112 b h
  · exact family_recover_113 b h
  · exact family_recover_120 b h
  · exact family_recover_121 b h
  · exact family_recover_122 b h
  · exact family_recover_123 b h
  · exact family_recover_130 b h
  · exact family_recover_131 b h
  · exact family_recover_132 b h
  · exact family_recover_133 b h
  · exact family_recover_200 b h
  · exact family_recover_201 b h
  · exact family_recover_202 b h
  · exact family_recover_203 b h
  · exact family_recover_210 b h
  · exact family_recover_211 b h
  · exact family_recover_212 b h
  · exact family_recover_213 b h
  · exact family_recover_220 b h
  · exact family_recover_221 b h
  · exact family_recover_222 b h
  · exact family_recover_223 b h
  · exact family_recover_230 b h
  · exact family_recover_231 b h
  · exact family_recover_232 b h
  · exact family_recover_233 b h
  · exact family_recover_300 b h
  · exact family_recover_301 b h
  · exact family_recover_302 b h
  · exact family_recover_303 b h
  · exact family_recover_310 b h
  · exact family_recover_311 b h
  · exact family_recover_312 b h
  · exact family_recover_313 b h
  · exact family_recover_320 b h
  · exact family_recover_321 b h
  · exact family_recover_322 b h
  · exact family_recover_323 b h
  · exact family_recover_330 b h
  · exact family_recover_331 b h
  · exact family_recover_332 b h
  · exact family_recover_333 b h

theorem shifted_in_family (s : State) (δ : Fin 4) (h : phaseTest s δ) :
    ∃ p : FamilyParameters, shiftedOdd s δ=shiftedOdd (familyState p) 0 := by
  refine ⟨recoverFamily (shiftState s δ) 0,?_⟩
  have he := phase_test_in_family (shiftState s δ) ((phaseTest_shift s δ).mpr h)
  rw [←he,shiftedOdd_shift]

end Holant.Certificates.FourthRootOdd
