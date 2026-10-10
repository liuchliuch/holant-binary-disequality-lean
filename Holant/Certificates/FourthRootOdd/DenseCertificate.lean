import Holant.Certificates.FourthRootOdd.DenseBlocks0
import Holant.Certificates.FourthRootOdd.DenseBlocks1
import Holant.Certificates.FourthRootOdd.DenseBlocks2
import Holant.Certificates.FourthRootOdd.DenseBlocks3
import Holant.Certificates.FourthRootOdd.DenseBlocks4
import Holant.Certificates.FourthRootOdd.DenseBlocks5
import Holant.Certificates.FourthRootOdd.DenseBlocks6
import Holant.Certificates.FourthRootOdd.DenseBlocks7
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem family_witness_correct (p : FamilyParameters) :
    ValidFamilyWitness p (printedFamilyWitness p) := by
  rcases p with ⟨⟨i,j,k⟩,x,y,z⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact dense_witness_000 x y z
  · exact dense_witness_001 x y z
  · exact dense_witness_002 x y z
  · exact dense_witness_003 x y z
  · exact dense_witness_010 x y z
  · exact dense_witness_011 x y z
  · exact dense_witness_012 x y z
  · exact dense_witness_013 x y z
  · exact dense_witness_020 x y z
  · exact dense_witness_021 x y z
  · exact dense_witness_022 x y z
  · exact dense_witness_023 x y z
  · exact dense_witness_030 x y z
  · exact dense_witness_031 x y z
  · exact dense_witness_032 x y z
  · exact dense_witness_033 x y z
  · exact dense_witness_100 x y z
  · exact dense_witness_101 x y z
  · exact dense_witness_102 x y z
  · exact dense_witness_103 x y z
  · exact dense_witness_110 x y z
  · exact dense_witness_111 x y z
  · exact dense_witness_112 x y z
  · exact dense_witness_113 x y z
  · exact dense_witness_120 x y z
  · exact dense_witness_121 x y z
  · exact dense_witness_122 x y z
  · exact dense_witness_123 x y z
  · exact dense_witness_130 x y z
  · exact dense_witness_131 x y z
  · exact dense_witness_132 x y z
  · exact dense_witness_133 x y z
  · exact dense_witness_200 x y z
  · exact dense_witness_201 x y z
  · exact dense_witness_202 x y z
  · exact dense_witness_203 x y z
  · exact dense_witness_210 x y z
  · exact dense_witness_211 x y z
  · exact dense_witness_212 x y z
  · exact dense_witness_213 x y z
  · exact dense_witness_220 x y z
  · exact dense_witness_221 x y z
  · exact dense_witness_222 x y z
  · exact dense_witness_223 x y z
  · exact dense_witness_230 x y z
  · exact dense_witness_231 x y z
  · exact dense_witness_232 x y z
  · exact dense_witness_233 x y z
  · exact dense_witness_300 x y z
  · exact dense_witness_301 x y z
  · exact dense_witness_302 x y z
  · exact dense_witness_303 x y z
  · exact dense_witness_310 x y z
  · exact dense_witness_311 x y z
  · exact dense_witness_312 x y z
  · exact dense_witness_313 x y z
  · exact dense_witness_320 x y z
  · exact dense_witness_321 x y z
  · exact dense_witness_322 x y z
  · exact dense_witness_323 x y z
  · exact dense_witness_330 x y z
  · exact dense_witness_331 x y z
  · exact dense_witness_332 x y z
  · exact dense_witness_333 x y z

def hasNativeRankOne (p : FamilyParameters) : Bool :=
  (List.ofFn (nativePair (familyState p))).any rankOneTest

theorem affine_native_loop_histogram :
    ((Finset.univ : Finset FamilyParameters).filter (fun p => hasNativeRankOne p=true)).card=336 ∧
    ((Finset.univ : Finset FamilyParameters).filter (fun p => hasNativeRankOne p=false)).card=176 := by decide

end Holant.Certificates.FourthRootOdd
