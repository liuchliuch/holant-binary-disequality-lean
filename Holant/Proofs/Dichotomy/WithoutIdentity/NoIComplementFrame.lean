import Holant.Proofs.Dichotomy.WithoutIdentity.NoIWeightedEqualityFrame
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Balance

/-! Exact native-X-preserving endpoint balance for a complementary-middle
quaternary. All middle entries stay unchanged; the common scalar is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIComplementFrame
open Holant Holant.Tractable
namespace W
export NoIWeightedEqualityFrame (basis native)
end W
namespace E
export Holant.LocalDrafts.Hardness.EightVertexNonexception (table)
end E
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false

theorem balanced (a b c d x r : AlgebraicComplex) (xn : x≠0) (rn : r≠0)
    (root : r^8=a/x) :
    (W.basis r rn).symm.action (E.table ⟨a,b,c,d,d,c,b,x⟩)=S.row (x*r^4) b c d := by
  have corner : a=x*r^8 := by
    have h:=(eq_div_iff xn).mp root
    linear_combination -h
  subst a
  have matrix : (W.basis r rn).inverse=diagonalKernel r⁻¹ r := by
    funext p q
    cases p <;> cases q <;> simp [NoIWeightedEqualityFrame.basis,
      GlobalCloseCompletionSymmetricGHZFrame.diagonalBasis,
      GlobalCloseCompletionSymmetricGHZFrame.diagonal,diagonalKernel]
  change Signature.coordinateAction (fun _=>(W.basis r rn).inverse) _=_
  rw [matrix]
  change Signature.coordinateAction (fun _=>diagonalKernel r⁻¹ r) (E.table ⟨x*r^8,b,c,d,d,c,b,x⟩)=_
  rw [coordinateAction_diagonal]
  funext z
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;> cases h3 : z 3 <;>
    simp [diagonalCoefficient,Fin.prod_univ_four,E.table,S.row,h0,h1,h2,h3] <;>
    field_simp <;> ring

structure Frame (a b c d x : AlgebraicComplex) where
  basis : InvertibleKernel
  scalar : AlgebraicComplex
  nonzero : scalar≠0
  native : Kernel.pullback Signature.disequality basis.matrix=Signature.disequality
  row : basis.symm.action (E.table ⟨a,b,c,d,d,c,b,x⟩)=S.row scalar b c d

def produce (a b c d x : AlgebraicComplex) (an : a≠0) (xn : x≠0) : Frame a b c d x := by
  classical
  apply Classical.choice
  letI : IsAlgClosed AlgebraicComplex:=IsAlgClosure.isAlgClosed ℚ
  obtain ⟨r,hr⟩:=IsAlgClosed.exists_pow_nat_eq (a/x) (by decide : 0<8)
  have rn : r≠0 := by
    intro zero
    rw [zero,zero_pow (by decide)] at hr
    exact div_ne_zero an xn hr.symm
  exact ⟨⟨W.basis r rn,x*r^4,mul_ne_zero xn (pow_ne_zero _ rn),W.native r rn,
    balanced a b c d x r xn rn hr⟩⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIComplementFrame
end
