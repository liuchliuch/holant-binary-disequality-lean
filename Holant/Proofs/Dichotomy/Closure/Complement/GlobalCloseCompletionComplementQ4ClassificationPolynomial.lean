import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationCircuit
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationAlgebra

/-! Literal coefficient calculation of the four-copy native-X circuit.
All six internal bits are summed, so the formula retains every scalar. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationPolynomial
open Holant
namespace S
export GlobalCloseCompletionComplementQ4Series (row spectrum ofSpectrum)
end S
namespace C
export GlobalCloseCompletionComplementQ4ClassificationCircuit (circuit value term circuit_value output denote)
end C
namespace A
export GlobalCloseCompletionComplementQ4ClassificationAlgebra (outerLeft outerRight middle)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K]

theorem value (a b c d : K) : C.circuit (S.row a b c d)=
    S.row (A.outerLeft a b c d) (A.outerRight a b c d) (A.middle a b c d) (A.middle a b c d) := by
  funext x
  rw [C.circuit_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [C.value,C.term,Fintype.sum_bool,S.row,
      Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3,
      A.outerLeft,A.outerRight,A.middle] <;> ring

variable [Algebra ℚ K] {r : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (arity i.val))
variable (N : NativeAntiTargetSource.Output H 4)

theorem output_value (a b c d : K) (form : N.network.denote=S.row a b c d) :
    (C.output H N).network.denote=
      S.row (A.outerLeft a b c d) (A.outerRight a b c d) (A.middle a b c d) (A.middle a b c d) := by
  rw [C.denote,form,value]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationPolynomial
end
