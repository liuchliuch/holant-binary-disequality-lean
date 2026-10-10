import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenCompose
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalPairTable

/-! A full antidiagonal available as an actual even block can flip inputs
of other even blocks. Opposite guard orientations retain one uniform nonzero
factor. The construction never installs an even block as a binary graph row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiSigned
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace B
export OrdinaryNegativeSparseMixingSource (Block trace_zero)
end B
namespace P
export OrdinaryNegativeXUniversalPair (arity table)
end P
namespace C
export NoXGeneralEvenCompose (block block_value family)
end C
namespace S
export NoXWeightedAntiSigned (anti recipe trace_value)
end S
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s n : ℕ} {b : ℕ→ℕ}
variable (row : B.Block (s:=s) (b:=b) n) (antiRow : B.Block (s:=s) (b:=b) 2)

def resources (i : Fin 2) : B.Block (s:=s) (b:=b) (P.arity n 2 i.val) :=
  match i with
  | ⟨0,_⟩=>row
  | ⟨1,_⟩=>antiRow
  | ⟨k+2,h⟩=>False.elim (by omega)

def base : Recipe (u:=1) (s:=2) (a:=fun _=>n) (b:=P.arity n 2) :=
  fun _=>[⟨0,fun i=>.inr i⟩]

variable (sign : Fin n→Bool)

def outer : Recipe (u:=1) (s:=2) (a:=fun _=>n+(n+0)) (b:=P.arity n 2) :=
  S.recipe (k:=0) (base (n:=n)) (fun _=>sign) 1 rfl

def block : B.Block (s:=s) (b:=b) n := C.block (l:=n+0) (outer sign) (resources row antiRow)

variable {K : Type} [Field K] [Algebra ℚ K] (H : (j : Fin s)→Signature K (b j.val))
variable (v w : K) (anti : antiRow.signature H=S.anti v w)

omit [Algebra ℚ K] in
theorem resource_value : C.family (resources row antiRow) H=P.table (row.signature H) (antiRow.signature H) := by
  funext i
  fin_cases i <;> rfl

omit [Algebra ℚ K] in
include anti in
theorem anti_literal :
    (⟨P.arity n 2 1,C.family (resources row antiRow) H (1 : Fin 2)⟩ : AnySignature K)=⟨2,S.anti v w⟩ := by
  change (⟨2,antiRow.signature H⟩ : AnySignature K)=_
  exact congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) anti

theorem base_value (x : Fin n→Bool) :
    M.trace (C.family (resources row antiRow) H) 0 (base (n:=n)) 0 x=row.signature H x := by
  rw [B.trace_zero]
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    base,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  rfl

include anti in
theorem block_value (x : Fin n→Bool) :
    (block row antiRow sign).signature H x=(v*w)^n*row.signature H (fun i=>Bool.xor (sign i) (x i)) := by
  rw [block,C.block_value]
  change M.trace (C.family (resources row antiRow) H) (n+0)
    (S.recipe (k:=0) (base (n:=n)) (fun _=>sign) 1 rfl) 0 x=_
  erw [S.trace_value (k:=0) (base (n:=n)) (fun _=>sign) 1 (C.family (resources row antiRow) H)
    v w (anti_literal row antiRow H v w anti)]
  rw [base_value]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenAntiSigned
end
