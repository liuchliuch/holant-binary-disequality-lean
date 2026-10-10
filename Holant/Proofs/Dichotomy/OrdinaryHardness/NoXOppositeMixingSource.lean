import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOppositeMixingSemantics

/-! Flatten both doubled odd resources into the original coefficient table.
Every positive and negative occurrence is retained by the even outer mixer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeMixingSource
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeXUniversalResource
namespace L
export NoXOppositeMixingLift (base lift even opposite compressed)
end L
namespace P
export OrdinaryNegativeXUniversalPair (arity)
end P
namespace C
export OrdinaryNegativeMixedBlockPrivateComposeCore (OddPrivate)
export OrdinaryNegativeMixedBlockPrivateComposeValue (rows)
export OrdinaryNegativeMixedBlockPrivateComposeSource (block block_value)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (ka kb : Kind)
variable (first : OddResource (s:=s) b (ka.arity+ka.arity))
variable (second : OddResource (s:=s) b (kb.arity+kb.arity))
def arity (i : ℕ) := P.arity ka.arity kb.arity i+P.arity ka.arity kb.arity i

def resource (i : Fin 2) : OddResource (s:=s) b (arity ka kb i.val) :=
  match i with
  | ⟨0,_⟩=>first
  | ⟨1,_⟩=>second
  | ⟨j+2,h⟩=>False.elim (by omega)

def privateCounts (i : Fin 2) := (resource ka kb first second i).privateCount

def inner (i : Fin 2) : Recipe (u:=1) (s:=s)
    (a:=fun _=>arity ka kb i.val+privateCounts ka kb first second i) (b:=b) :=
  (resource ka kb first second i).rows

theorem inner_odd : C.OddPrivate (privateCounts ka kb first second) (inner ka kb first second) := by
  intro i
  exact ⟨(resource ka kb first second i).constant_even,
    (resource ka kb first second i).boundary_odd,(resource ka kb first second i).private_even⟩

def output : OrdinaryNegativeSparseMixingSource.Block (s:=s) (b:=b)
    (NoXOppositeMixingLift.size ka kb+NoXOppositeMixingLift.size ka kb) :=
  C.block (l:=0) (b:=arity ka kb) (c:=b) (L.lift (L.base ka kb))
    (privateCounts ka kb first second) (inner ka kb first second)
    (inner_odd ka kb first second) (L.even ka kb)

def ambient (i : Fin 2) : Signature AlgebraicComplex (arity ka kb i.val) :=
  (resource ka kb first second i).ambient H

theorem output_value (x) :
    ((output ka kb first second).signature H x : AlgebraicComplex)=
      coefficient (ambient H ka kb first second) (L.lift (L.base ka kb)) 0 x := by
  rw [output,C.block_value,OrdinaryNegativeSparseMixingSource.trace_zero]
  change (K.subtype : K→+*AlgebraicComplex) _ = _
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    map_list_prod,List.map_map,Function.comp_def]
  congr 1

def logicalFirst : Signature AlgebraicComplex ka.arity := fun x=>first.ambient H (L.opposite x)
def logicalSecond : Signature AlgebraicComplex kb.arity := fun x=>second.ambient H (L.opposite x)

variable (alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (logicalFirst H ka first)))
variable (affine : Affine (logicalSecond H kb second))
variable (full_f : ∀x,logicalFirst H ka first (ka.code x)≠0)
variable (full_g : ∀x,logicalSecond H kb second (kb.code x)≠0)
include alpha affine full_f full_g in
theorem evenBad : EvenBad H := by
  refine ⟨_,output ka kb first second,?_⟩
  have bad:=NoXOppositeMixingSemantics.lifted_bad ka kb
    (logicalFirst H ka first) (logicalSecond H kb second) alpha affine full_f full_g
    (ambient H ka kb first second) (by funext i;fin_cases i <;> rfl)
  have he : (fun x=>((output ka kb first second).signature H x : AlgebraicComplex))=
      coefficient (ambient H ka kb first second) (L.lift (L.base ka kb)) 0 :=
    funext (output_value H ka kb first second)
  rwa [he]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeMixingSource
end
