import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralZBinaryAlgebra
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralZSign
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenCompose
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalPairTable

/-! Four actual copies of a binary even resource and the retained Z produce
the exact filtered binary. The first-row unary weights are literal pinnings
of those copies; no reciprocal or negation resource is presumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralZBinaryBlock
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
namespace Z
export NoXGeneralZSign (signature rows balanced coefficient_value)
end Z
namespace A
export NoXGeneralZBinaryAlgebra (filtered)
end A
namespace M
export OrdinaryNegativeMixedBlockSource (trace)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (b i.val)) (label : Fin s)
variable (literal : (⟨b label.val,H label⟩ : AnySignature K)=⟨2,Z.signature⟩)

def signBlock : B.Block (s:=s) (b:=b) 1 :=
  ⟨0,Z.rows H label literal (.inr 0),Z.balanced H label literal (.inr 0)⟩

theorem sign_value (x : Fin 1→Bool) : (signBlock H label literal).signature H x=if x 0 then -1 else 1 := by
  change M.trace H 0 (Z.rows H label literal (.inr 0)) 0 x=_
  rw [B.trace_zero,Z.coefficient_value]
  rfl

variable (row : B.Block (s:=s) (b:=b) 2)

def resources (i : Fin 2) : B.Block (s:=s) (b:=b) (P.arity 2 1 i.val) :=
  match i with
  | ⟨0,_⟩=>row
  | ⟨1,_⟩=>signBlock H label literal
  | ⟨k+2,h⟩=>False.elim (by omega)

def outer : Recipe (u:=1) (s:=2) (a:=fun _=>2+1) (b:=P.arity 2 1) := fun _=>[
  ⟨0,![.inr (0 : Fin 3),.inr (2 : Fin 3)]⟩,⟨0,![.inr (1 : Fin 3),.inr (2 : Fin 3)]⟩,
  ⟨0,![.inl false,.inr (2 : Fin 3)]⟩,⟨0,![.inl false,.inr (2 : Fin 3)]⟩,⟨1,fun _=>.inr (2 : Fin 3)⟩]

def block : B.Block (s:=s) (b:=b) 2 := C.block (l:=1) outer (resources H label literal row)

theorem family_value : C.family (resources H label literal row) H=
    P.table (row.signature H) (fun x=>if x 0 then -1 else 1) := by
  funext i
  fin_cases i
  · rfl
  · exact funext (sign_value H label literal)

omit [Algebra ℚ K] in
theorem coefficient_value (f : Signature K 2) (g : Signature K 1) (x : Fin 2→Bool) (q : Bool) :
    coefficient (P.table f g) outer 0 (Fin.addCases x (fun _=>q))=
      f ![x 0,q]*f ![x 1,q]*f ![false,q]^2*g (fun _=>q) := by
  let bits : Fin 3→Bool := Fin.addCases (m := 2) (n := 1) (motive := fun _=>Bool) x (fun _=>q)
  have p0 : (fun j : Fin 2=>Sum.elim id bits (![.inr (0 : Fin 3),.inr (2 : Fin 3)] j))=![x 0,q] := by
    funext j
    fin_cases j <;> rfl
  have p1 : (fun j : Fin 2=>Sum.elim id bits (![.inr (1 : Fin 3),.inr (2 : Fin 3)] j))=![x 1,q] := by
    funext j
    fin_cases j <;> rfl
  have pc : (fun j : Fin 2=>Sum.elim id bits (![.inl false,.inr (2 : Fin 3)] j))=![false,q] := by
    funext j
    fin_cases j <;> rfl
  have ps : (fun _ : Fin 1=>Sum.elim id bits (.inr (2 : Fin 3)))=(fun _=>q) := rfl
  change coefficient (P.table f g) outer 0 bits=_
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    outer,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,P.table]
  erw [p0,p1,pc,ps]
  ring

theorem value (x : Fin 2→Bool) : (block H label literal row).signature H x=A.filtered (row.signature H) x := by
  rw [block,C.block_value,family_value]
  unfold M.trace
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  change (∑q : Bool,coefficient (P.table (row.signature H) (fun z=>if z 0 then -1 else 1)) outer 0
    (Fin.addCases x (fun _=>q)))=_
  simp_rw [coefficient_value]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,mul_one,mul_neg_one,A.filtered]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralZBinaryBlock
end
