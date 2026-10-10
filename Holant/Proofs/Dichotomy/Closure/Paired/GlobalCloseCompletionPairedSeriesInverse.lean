import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCaps
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZInverseFinite

/-! Every actual nonsingular diagonal has a literal scalar inverse in a
source-preserving finite extension. Equal entries use the original graph;
distinct entries use the already proved positive-power/finite-target source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesInverse
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
namespace P
export GlobalCloseCompletionPairedSeriesCaps (output)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal mul)
end D
namespace I
export GlobalCloseCompletionSymmetricGHZInverse (matrix)
export GlobalCloseCompletionSymmetricGHZInverseFinite (Extension produce)
end I
namespace A
export NoXOrdinaryGraphAdjoin (arity signatures old old_literal newLabel new_literal source)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s degree : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val)) (F : FixedField K degree)
variable (N : M.Macro H 2) (a d : K) (ha : a≠0) (hd : d≠0)
variable (form : N.network.denote=binarySignature (D.diagonal a d))

include form in
theorem matrix : I.matrix H (P.output N)=D.diagonal a d := by
  funext i j
  change N.network.denote ![i,j]=_
  rw [form]
  rfl

def produce : I.Extension H F (P.output N) := by
  classical
  by_cases same : a=d
  · subst d
    let B:=D.diagonal a a
    have product : B*B=a^2 • (1 : Matrix Bool Bool K) := by
      rw [D.mul]
      ext i j
      cases i <;> cases j <;> simp [D.diagonal,Matrix.one_apply,pow_two]
    exact {
      count:=s+1
      b:=A.arity H (P.output N)
      table:=A.signatures F H (P.output N)
      old:=A.old H
      old_literal:=A.old_literal F H (P.output N)
      inverse:=B
      scalar:=a^2
      nonzero:=pow_ne_zero _ ha
      label:=A.newLabel H
      literal:=(A.new_literal F H (P.output N)).trans (congrArg
        (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) form)
      left_inverse:=by rw [matrix H N a a form];exact product
      right_inverse:=by rw [matrix H N a a form];exact product
      source:=A.source F H (P.output N) }
  · apply I.produce H F (P.output N) a d same ha hd
    · rw [matrix H N a d form]
      simp [Matrix.trace,D.diagonal]
      ring
    · rw [matrix H N a d form,Holant.Complexity.BinaryInterpolation.det_entries]
      simp [D.diagonal]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesInverse
end
