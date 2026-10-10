import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeAntiGroup
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeFiniteCaps
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseActual

/-! Three actual native-X weighted self-caps. The phase is attached as an
actual antidiagonal binary, then the same native edge closes the selected
pair. The actual contraction multiplier remains recorded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOddCards
open Holant Holant.OpenNetworkComposition
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
namespace R
export PaperTerminalBridgeEqualProductsCaps (unscale)
end R
namespace A
export PaperTerminalBridgeAntiGroup (Available)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

def order (k : Fin 3) : Equiv.Perm (Fin 4) where
  toFun := ![![0,1,2,3],![0,2,1,3],![2,3,1,0]] k
  invFun := ![![0,1,2,3],![0,2,1,3],![3,2,0,1]] k
  left_inv := by fin_cases k <;> decide
  right_inv := by fin_cases k <;> decide

def pencil (e : Entries K) (k : Fin 3) (t : K) : K×K :=
  ![(e.w+t*e.c,e.z+t*e.d),(e.w+t*e.b,e.y+t*e.d),(e.c+t*e.d,e.w+t*e.z)] k

def card (f : Signature K 4) (k : Fin 3) (t : K) : Signature K 2 :=
  Signature.contract Signature.disequality
    (fun x=>(if x 1 then t else 1)*Tensor.reindex (order k) f x)

theorem form (f : Signature K 4) (even : EvenSupport f) (k : Fin 3) (t : K) :
    card f k t=C.antiTensor (pencil (entries f) k t).1 (pencil (entries f) k t).2 := by
  funext x
  rw [card,Signature.contract_disequality]
  rw [←table_entries f even]
  fin_cases k <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Tensor.reindex,order,pencil,C.antiTensor,entries,table,h0,h1,add_comm]

theorem actual (F : SignatureFamily K) (f : Signature K 4)
    (actualF : Gadget.Realizes F .disequality f) (k : Fin 3) (t : K)
    (phase : A.Available F t) : Gadget.RealizesUpTo F .disequality (card f k t) := by
  obtain ⟨c,hc,actualC⟩ := phase
  have ordered := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality f actualF
    (order k).symm
  simp only [Equiv.symm_symm] at ordered
  have attached := realizes_splice F (Tensor.reindex (order k) f)
    (fun x=>c*C.antiTensor 1 t x) ordered actualC 1
  have value : spliceTensor (Tensor.reindex (order k) f) (fun x=>c*C.antiTensor 1 t x) 1=
      fun x=>c*((if x 1 then t else 1)*Tensor.reindex (order k) f x) := by
    funext x
    cases hx : x 1 <;>
      simp [spliceTensor,C.antiTensor,Signature.disequality,hx,Function.update_eq_self]
    all_goals rw [←hx,Function.update_eq_self] <;> ring
  rw [value] at attached
  have closed := realizes_contract F _ attached (by norm_num)
  rw [contract_scale] at closed
  exact R.unscale F (card f k t) c hc closed

theorem actual_pencil (F : SignatureFamily K) (f : Signature K 4)
    (actualF : Gadget.Realizes F .disequality f) (even : EvenSupport f)
    (k : Fin 3) (t : K) (phase : A.Available F t) :
    Gadget.RealizesUpTo F .disequality
      (C.antiTensor (pencil (entries f) k t).1 (pencil (entries f) k t).2) := by
  rw [←form f even k t]
  exact actual F f actualF k t phase

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOddCards
end
