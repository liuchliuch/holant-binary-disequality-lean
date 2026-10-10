import Holant.Certificates.FourthRootOdd.PhaseBlocks0
import Holant.Certificates.FourthRootOdd.PhaseBlocks1
import Holant.Certificates.FourthRootOdd.PhaseBlocks2
import Holant.Certificates.FourthRootOdd.PhaseBlocks3
import Holant.Certificates.FourthRootOdd.PhaseBlocks4
import Holant.Certificates.FourthRootOdd.PhaseBlocks5
import Holant.Certificates.FourthRootOdd.PhaseBlocks6
import Holant.Certificates.FourthRootOdd.PhaseBlocks7
import Holant.Certificates.FourthRootOdd.PhaseWitness

namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops Holant.Tractable

theorem remaining_phase_test (s : State) (h : classify s=.remaining) (hn : ¬Exceptional s) :
    phaseTest s 0 ∨ phaseTest s 1 := by
  rcases s with ⟨⟨i,j,k⟩,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact phase_dispatch_000 b h hn
  · exact phase_dispatch_001 b h hn
  · exact phase_dispatch_002 b h hn
  · exact phase_dispatch_003 b h hn
  · exact phase_dispatch_010 b h hn
  · exact phase_dispatch_011 b h hn
  · exact phase_dispatch_012 b h hn
  · exact phase_dispatch_013 b h hn
  · exact phase_dispatch_020 b h hn
  · exact phase_dispatch_021 b h hn
  · exact phase_dispatch_022 b h hn
  · exact phase_dispatch_023 b h hn
  · exact phase_dispatch_030 b h hn
  · exact phase_dispatch_031 b h hn
  · exact phase_dispatch_032 b h hn
  · exact phase_dispatch_033 b h hn
  · exact phase_dispatch_100 b h hn
  · exact phase_dispatch_101 b h hn
  · exact phase_dispatch_102 b h hn
  · exact phase_dispatch_103 b h hn
  · exact phase_dispatch_110 b h hn
  · exact phase_dispatch_111 b h hn
  · exact phase_dispatch_112 b h hn
  · exact phase_dispatch_113 b h hn
  · exact phase_dispatch_120 b h hn
  · exact phase_dispatch_121 b h hn
  · exact phase_dispatch_122 b h hn
  · exact phase_dispatch_123 b h hn
  · exact phase_dispatch_130 b h hn
  · exact phase_dispatch_131 b h hn
  · exact phase_dispatch_132 b h hn
  · exact phase_dispatch_133 b h hn
  · exact phase_dispatch_200 b h hn
  · exact phase_dispatch_201 b h hn
  · exact phase_dispatch_202 b h hn
  · exact phase_dispatch_203 b h hn
  · exact phase_dispatch_210 b h hn
  · exact phase_dispatch_211 b h hn
  · exact phase_dispatch_212 b h hn
  · exact phase_dispatch_213 b h hn
  · exact phase_dispatch_220 b h hn
  · exact phase_dispatch_221 b h hn
  · exact phase_dispatch_222 b h hn
  · exact phase_dispatch_223 b h hn
  · exact phase_dispatch_230 b h hn
  · exact phase_dispatch_231 b h hn
  · exact phase_dispatch_232 b h hn
  · exact phase_dispatch_233 b h hn
  · exact phase_dispatch_300 b h hn
  · exact phase_dispatch_301 b h hn
  · exact phase_dispatch_302 b h hn
  · exact phase_dispatch_303 b h hn
  · exact phase_dispatch_310 b h hn
  · exact phase_dispatch_311 b h hn
  · exact phase_dispatch_312 b h hn
  · exact phase_dispatch_313 b h hn
  · exact phase_dispatch_320 b h hn
  · exact phase_dispatch_321 b h hn
  · exact phase_dispatch_322 b h hn
  · exact phase_dispatch_323 b h hn
  · exact phase_dispatch_330 b h hn
  · exact phase_dispatch_331 b h hn
  · exact phase_dispatch_332 b h hn
  · exact phase_dispatch_333 b h hn

/-- Every nonexceptional remaining state has the certified analytic phase shift
in the actual source affine class. The shift is not claimed as a free gadget. -/
theorem remaining_affine_shift (s : State) (h : classify s=.remaining) (hn : ¬Exceptional s) :
    ∃ δ : Fin 4, (δ=0 ∨ δ=1) ∧ Affine (shiftedOdd s δ) := by
  rcases remaining_phase_test s h hn with h₀ | h₁
  · exact ⟨0,Or.inl rfl,shiftedOdd_affine s 0 h₀⟩
  · exact ⟨1,Or.inr rfl,shiftedOdd_affine s 1 h₁⟩

end Holant.Certificates.FourthRootOdd
