import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Series
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsWCore
import Holant.Tractable.Conformal.MatrixSupport
import Holant.Tractable.SymmetricBinaryPullback.Basic

/-! A genuine common diagonal chart balances the two nonzero corners
without changing complementary middle-pair equality. Its exact native-X
scalar is retained; fourth roots describe the chart, never free gates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Balance
open Holant Holant.Tractable
namespace E
export Holant.LocalDrafts.Hardness.EightVertexNonexception (table)
end E
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant invertibleOfDeterminant)
end B
set_option maxHeartbeats 400000
set_option Elab.async false

def basis (r : AlgebraicComplex) (nonzero : r≠0) : InvertibleKernel:=
  B.invertibleOfDeterminant (diagonalKernel 1 r) (by simpa [B.determinant,diagonalKernel] using nonzero)

theorem native_edge (r : AlgebraicComplex) (nonzero : r≠0) :
    Kernel.pullback Signature.disequality (basis r nonzero).matrix=
      fun p q=>r*Signature.disequality p q := by
  change Kernel.pullback Signature.disequality (diagonalKernel 1 r)=_
  funext p q
  cases p <;> cases q <;> simp [Kernel.pullback,Kernel.mul_apply,Kernel.transpose,diagonalKernel,Signature.disequality,Fintype.sum_bool]

theorem conformal (r : AlgebraicComplex) (nonzero : r≠0) : XConformal (basis r nonzero):=
  ⟨r,nonzero,native_edge r nonzero⟩

theorem balanced (a b c d x r : AlgebraicComplex) (xn : x≠0) (rn : r≠0) (root : r^4=a/x) :
    (basis r rn).action (E.table ⟨a,b,c,d,d,c,b,x⟩)=S.row a (r^2*b) (r^2*c) (r^2*d) := by
  have corner : r^4*x=a:=(eq_div_iff xn).mp root
  change Signature.coordinateAction (fun _=>diagonalKernel 1 r) (E.table ⟨a,b,c,d,d,c,b,x⟩)=_
  rw [coordinateAction_diagonal]
  funext z
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    simp [diagonalCoefficient,Fin.prod_univ_four,E.table,S.row,h0,h1,h2,h3,pow_two]
  all_goals linear_combination corner

theorem root (a x : AlgebraicComplex) (an : a≠0) (xn : x≠0) :
    ∃r : AlgebraicComplex,r≠0 ∧ r^4=a/x := by
  letI : IsAlgClosed AlgebraicComplex:=IsAlgClosure.isAlgClosed ℚ
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_pow_nat_eq (a/x) (by decide : 0<4)
  refine ⟨r,?_,hr⟩
  intro zero
  rw [zero,zero_pow (by decide : 4≠0)] at hr
  exact (div_ne_zero an xn) hr.symm


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Balance
end
