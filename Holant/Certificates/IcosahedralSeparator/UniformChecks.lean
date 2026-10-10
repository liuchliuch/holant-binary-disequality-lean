import Holant.Certificates.IcosahedralSeparator.UniformCheck29
import Holant.Certificates.IcosahedralSeparator.UniformSemanticBridge

namespace Holant.Certificates.IcosahedralSeparator

theorem uniform_rank_checks (i : Fin 30) : UniformRankCheck i := by
  fin_cases i
  · exact uniformRankCheck_00
  · exact uniformRankCheck_01
  · exact uniformRankCheck_02
  · exact uniformRankCheck_03
  · exact uniformRankCheck_04
  · exact uniformRankCheck_05
  · exact uniformRankCheck_06
  · exact uniformRankCheck_07
  · exact uniformRankCheck_08
  · exact uniformRankCheck_09
  · exact uniformRankCheck_10
  · exact uniformRankCheck_11
  · exact uniformRankCheck_12
  · exact uniformRankCheck_13
  · exact uniformRankCheck_14
  · exact uniformRankCheck_15
  · exact uniformRankCheck_16
  · exact uniformRankCheck_17
  · exact uniformRankCheck_18
  · exact uniformRankCheck_19
  · exact uniformRankCheck_20
  · exact uniformRankCheck_21
  · exact uniformRankCheck_22
  · exact uniformRankCheck_23
  · exact uniformRankCheck_24
  · exact uniformRankCheck_25
  · exact uniformRankCheck_26
  · exact uniformRankCheck_27
  · exact uniformRankCheck_28
  · exact uniformRankCheck_29

theorem uniform_outside_checks (i : Fin 30) : UniformOutsideCheck i := by
  fin_cases i
  · exact uniformOutsideCheck_00
  · exact uniformOutsideCheck_01
  · exact uniformOutsideCheck_02
  · exact uniformOutsideCheck_03
  · exact uniformOutsideCheck_04
  · exact uniformOutsideCheck_05
  · exact uniformOutsideCheck_06
  · exact uniformOutsideCheck_07
  · exact uniformOutsideCheck_08
  · exact uniformOutsideCheck_09
  · exact uniformOutsideCheck_10
  · exact uniformOutsideCheck_11
  · exact uniformOutsideCheck_12
  · exact uniformOutsideCheck_13
  · exact uniformOutsideCheck_14
  · exact uniformOutsideCheck_15
  · exact uniformOutsideCheck_16
  · exact uniformOutsideCheck_17
  · exact uniformOutsideCheck_18
  · exact uniformOutsideCheck_19
  · exact uniformOutsideCheck_20
  · exact uniformOutsideCheck_21
  · exact uniformOutsideCheck_22
  · exact uniformOutsideCheck_23
  · exact uniformOutsideCheck_24
  · exact uniformOutsideCheck_25
  · exact uniformOutsideCheck_26
  · exact uniformOutsideCheck_27
  · exact uniformOutsideCheck_28
  · exact uniformOutsideCheck_29

noncomputable section
open Holant Holant.Certificates.MatchingProductBridge

theorem uniform_output_ranks (i : Fin 30) (k : Fin 3) :
    Matrix.rank (flatten k (uniformOutput i))=3 :=
  uniform_rank_three_of_check i (uniform_rank_checks i) k

theorem uniform_subsequent_nonsingular (i : Fin 30) :
    Matrix.det (Matrix.of (subsequentOutput i))≠0 :=
  subsequent_nonsingular_of_check i (uniform_outside_checks i)

theorem uniform_subsequent_outside (i : Fin 30) :
    ¬groupDirection .icosahedral (Kernel.mul (subsequentOutput i) Signature.disequality) :=
  subsequent_transfer_outside_of_check i (uniform_outside_checks i)

 theorem uniform_subsequent_outside_matrix (i : Fin 30) :
    ¬groupDirection .icosahedral
      (Matrix.of (subsequentOutput i)*Matrix.of X) := by
  have he : Matrix.of (Kernel.mul (subsequentOutput i) Signature.disequality)=
      Matrix.of (subsequentOutput i)*Matrix.of X := by
    ext a b
    simp [Kernel.mul_apply,Matrix.mul_apply,X,add_comm]
  rw [←he]
  exact uniform_subsequent_outside i

end
end Holant.Certificates.IcosahedralSeparator
