import Holant.Projective.CyclicDressing.Action

/-! Algebraic interface for four disjoint one-port gadget attachments. The
identity preserves original boundary order. Realizability of onePort is a
separate graph-gluing obligation and is not postulated by this module. -/
noncomputable section
namespace Holant.Projective.CyclicDressing
open CyclicQuaternary.Physical

/-- The unchanged coordinates use literal equality action. -/
def onePort {n : ℕ} (q : Signature Scalar n) (i : Fin n) (C : Mat) : Signature Scalar n :=
  Signature.coordinateAction
    (fun j => if j=i then Kernel.mul C Signature.disequality else Signature.equality) q

/-- Four separate attachments coincide with the actual simultaneous finite sum. -/
theorem four_attachments (q : Signature Scalar 4) (C : Fin 4 → Mat) :
    onePort (onePort (onePort (onePort q 0 (C 0)) 1 (C 1)) 2 (C 2)) 3 (C 3)=
      physicalDressing q C := by
  simp only [onePort,Signature.coordinateAction_comp,physicalDressing]
  congr 1
  funext i
  fin_cases i <;> simp [Kernel.equality_mul,Kernel.mul_equality]

end Holant.Projective.CyclicDressing
