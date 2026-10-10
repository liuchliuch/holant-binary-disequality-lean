import Holant.Dihedral.CompatibleClosure.NativeCard
import Holant.OpenNetworkComposition.Closure

/-! Two-port connection is one safe disjoint splice followed by a native-X
self-contraction. The latter's projective realization is supplied separately. -/
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable Holant.OpenNetworkComposition
set_option backward.isDefEq.respectTransparency false

private theorem update_second {n : ℕ} (a b c : Bool) (x : Fin n → Bool) :
    Function.update (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) 1 c =
      Fin.cons a (Fin.cons c x) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp
  · simp
  · have hk : k.succ.succ ≠ (1 : Fin (n+2)) := Fin.succ_succ_ne_one k
    simp only [Function.update_of_ne hk,Fin.cons_succ]

/-- The exact four-sum identity retains the physical binary port orientation:
attach its port1 at original q port1, then close the first two outer ports. -/
theorem contract_splice_eq_nativeCard {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat) :
    Signature.contract Signature.disequality (spliceTensor q (kernelSignature C) 1) =
      nativeCardValue q C := by
  funext x
  rw [Signature.contract_disequality]
  simp only [spliceTensor,update_second,kernelSignature,Fin.cons_one,Fin.cons_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simp [Signature.disequality,nativeCardValue]
  ring

/-- The first connection always has exact same-family provenance, including
free stubs and scalar components. Only the subsequent self-contraction needs
the projective circle-handling theorem. -/
theorem realizes_first_connection {n : ℕ} (F : SignatureFamily Scalar)
    (q : Signature Scalar (n+2)) (C : Mat)
    (hq : Gadget.Realizes F .disequality q)
    (hc : Gadget.Realizes F .disequality (kernelSignature C)) :
    Gadget.Realizes F .disequality (spliceTensor q (kernelSignature C) 1) :=
  realizes_splice F q (kernelSignature C) hq hc 1

end Holant.Dihedral.CompatibleClosure
