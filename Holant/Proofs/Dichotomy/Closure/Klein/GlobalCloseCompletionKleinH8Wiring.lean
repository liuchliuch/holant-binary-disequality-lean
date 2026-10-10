import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH8Table
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMActual

/-! Six explicit I joins of two literal eight-port source copies. The source
port order is part of the checked equation, and every I join has an actual
retained-I/native-X implementation in the unchanged field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH8Wiring
open Holant Holant.Tractable Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace T
export GlobalCloseCompletionKleinH8Table (h8 raw joined joined_h8 joined_scale)
end T
namespace A
export GlobalCloseCompletionKleinH6RMActual (equality_contract_actual)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def order : Equiv.Perm (Fin 16) where
  toFun := ![12,13,0,2,4,6,8,10,3,9,14,5,1,15,11,7]
  invFun := ![2,12,3,8,4,11,5,15,6,9,7,14,0,1,10,13]
  left_inv := by decide
  right_inv := by decide

def join (f g : Signature K 8) : Signature K 4 :=
  Signature.contract Signature.equality (Signature.contract Signature.equality
    (Signature.contract Signature.equality (Signature.contract Signature.equality
      (Signature.contract Signature.equality (Signature.contract Signature.equality
        (Tensor.reindex order (Signature.tensor f g)))))))

theorem input (f g : Signature K 8) (x : Fin 4→Bool) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Bool) :
    Tensor.reindex order (Signature.tensor f g) (Fin.cons p0 (Fin.cons p1 (Fin.cons p2 (Fin.cons p3 (Fin.cons p4 (Fin.cons p5 (Fin.cons p6 (Fin.cons p7 (Fin.cons p8 (Fin.cons p9 (Fin.cons p10 (Fin.cons p11 x))))))))))))=
      f ![x 0,x 1,p0,p2,p4,p6,p8,p10]*g ![p3,p9,x 2,p5,p1,x 3,p11,p7] := by
  simp only [Tensor.reindex_apply,Signature.tensor_apply]
  congr 1
  · apply congrArg f
    funext i
    fin_cases i <;> rfl
  · apply congrArg g
    funext i
    fin_cases i <;> rfl

theorem value (f g : Signature K 8) (x : Fin 4→Bool) : join f g x=T.joined f g x := by
  simp only [join,Signature.contract_equality]
  rw [input f g x false false false false false false false false false false false false,
    input f g x false false false false false false false false false false true true,
    input f g x false false false false false false false false true true false false,
    input f g x false false false false false false false false true true true true,
    input f g x false false false false false false true true false false false false,
    input f g x false false false false false false true true false false true true,
    input f g x false false false false false false true true true true false false,
    input f g x false false false false false false true true true true true true,
    input f g x false false false false true true false false false false false false,
    input f g x false false false false true true false false false false true true,
    input f g x false false false false true true false false true true false false,
    input f g x false false false false true true false false true true true true,
    input f g x false false false false true true true true false false false false,
    input f g x false false false false true true true true false false true true,
    input f g x false false false false true true true true true true false false,
    input f g x false false false false true true true true true true true true,
    input f g x false false true true false false false false false false false false,
    input f g x false false true true false false false false false false true true,
    input f g x false false true true false false false false true true false false,
    input f g x false false true true false false false false true true true true,
    input f g x false false true true false false true true false false false false,
    input f g x false false true true false false true true false false true true,
    input f g x false false true true false false true true true true false false,
    input f g x false false true true false false true true true true true true,
    input f g x false false true true true true false false false false false false,
    input f g x false false true true true true false false false false true true,
    input f g x false false true true true true false false true true false false,
    input f g x false false true true true true false false true true true true,
    input f g x false false true true true true true true false false false false,
    input f g x false false true true true true true true false false true true,
    input f g x false false true true true true true true true true false false,
    input f g x false false true true true true true true true true true true,
    input f g x true true false false false false false false false false false false,
    input f g x true true false false false false false false false false true true,
    input f g x true true false false false false false false true true false false,
    input f g x true true false false false false false false true true true true,
    input f g x true true false false false false true true false false false false,
    input f g x true true false false false false true true false false true true,
    input f g x true true false false false false true true true true false false,
    input f g x true true false false false false true true true true true true,
    input f g x true true false false true true false false false false false false,
    input f g x true true false false true true false false false false true true,
    input f g x true true false false true true false false true true false false,
    input f g x true true false false true true false false true true true true,
    input f g x true true false false true true true true false false false false,
    input f g x true true false false true true true true false false true true,
    input f g x true true false false true true true true true true false false,
    input f g x true true false false true true true true true true true true,
    input f g x true true true true false false false false false false false false,
    input f g x true true true true false false false false false false true true,
    input f g x true true true true false false false false true true false false,
    input f g x true true true true false false false false true true true true,
    input f g x true true true true false false true true false false false false,
    input f g x true true true true false false true true false false true true,
    input f g x true true true true false false true true true true false false,
    input f g x true true true true false false true true true true true true,
    input f g x true true true true true true false false false false false false,
    input f g x true true true true true true false false false false true true,
    input f g x true true true true true true false false true true false false,
    input f g x true true true true true true false false true true true true,
    input f g x true true true true true true true true false false false false,
    input f g x true true true true true true true true false false true true,
    input f g x true true true true true true true true true true false false,
    input f g x true true true true true true true true true true true true]
  simp only [T.joined,Fintype.sum_bool]
  ac_rfl

theorem scale (f g : Signature K 8) (c d : K) : join (c • f) (d • g)=(c*d) • join f g := by
  funext x
  simp only [value,Pi.smul_apply,smul_eq_mul]
  exact congrFun (T.joined_scale f g c d) x

theorem h8_value (c : K) : join (c • (T.h8 : Signature K 8)) (c • T.h8)=c^2 • T.raw := by
  rw [scale]
  funext x
  change (c*c)*join T.h8 T.h8 x=c^2*T.raw x
  rw [value,T.joined_h8]
  ring

variable (F : SignatureFamily K) (identity : RetainsIdentity F)

include identity in
theorem actual (f g : Signature K 8) (left : Gadget.Realizes F .disequality f)
    (right : Gadget.Realizes F .disequality g) : Gadget.Realizes F .disequality (join f g) := by
  have tensor := realizes_tensor F .disequality f g left right
  have reordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality
    (Signature.tensor f g) tensor order.symm
  simp only [Equiv.symm_symm] at reordered
  exact A.equality_contract_actual F identity _ (A.equality_contract_actual F identity _
    (A.equality_contract_actual F identity _ (A.equality_contract_actual F identity _
      (A.equality_contract_actual F identity _ (A.equality_contract_actual F identity _ reordered)))))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH8Wiring
end
