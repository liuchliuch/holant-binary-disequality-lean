import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCoordinates
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralComplete
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicLift
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryAnchorX

/-! A literal ordinary equality-three graph yields equality-four by joining
two actual copies. Its whole-family terminal uses the existing implemented
pin and negative programmes; no Eq4 or hardness producer is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZEquality
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (eq3 eq3_value)
end C
namespace A
export GlobalCloseCompletionOrdinaryAnchorPins (data old_included)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option Elab.async false

def joinOrder : Equiv.Perm (Fin 6) where
  toFun := ![0,2,3,1,4,5]
  invFun := ![0,3,1,2,4,5]
  left_inv := by decide
  right_inv := by decide

variable {K : Type} [Field K] {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (b i.val))

def join (N : Macro H 3) : Macro H 4 := ((N.tensor N).reindex joinOrder).contract

theorem join_value (N : Macro H 3) (x : Fin 4→Bool) :
    (join H N).network.denote x=
      N.network.denote ![false,x 0,x 1]*N.network.denote ![false,x 2,x 3]+
      N.network.denote ![true,x 0,x 1]*N.network.denote ![true,x 2,x 3] := by
  rw [join,Macro.contract_denote,Macro.reindex_denote,Macro.tensor_denote]
  simp only [Tensor.reindex_apply,Signature.tensor_apply]
  have left (v : Bool) : (fun i : Fin 3=>(Fin.cons v (Fin.cons v x) : Fin 6→Bool) (joinOrder (Fin.castAdd 3 i)))=
      ![v,x 0,x 1] := by funext i; fin_cases i <;> rfl
  have right (v : Bool) : (fun i : Fin 3=>(Fin.cons v (Fin.cons v x) : Fin 6→Bool) (joinOrder (Fin.natAdd 3 i)))=
      ![v,x 2,x 3] := by funext i; fin_cases i <;> rfl
  simp only [left,right]

theorem join_eq4 (N : Macro H 3) (c : K)
    (form : N.network.denote=fun x=>c*C.eq3 x) :
    (join H N).network.denote=fun x=>c^2*Holant.EightVertex.ProductAnchor.equalityFour x := by
  funext x
  rw [join_value,form]
  simp only [C.eq3_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3,pow_two]

section Original
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (S : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F S).evaluate F) (OriginalForestSource.value G))
variable (N : Macro S 3) (c : L) (nonzero : c≠0)
variable (form : N.network.denote=fun x=>c*C.eq3 x)

def anchor : GlobalCloseCompletionOrdinaryAnchorInput.Input G where
  K := L
  degree := degree
  F := F
  count := r
  b := b
  H := S
  graph := (join S N).network
  labels := (join S N).labels
  exact := (join S N).exact
  ordinary := (join S N).edges
  scalar := c^2
  nonzero := pow_ne_zero _ nonzero
  denote := join_eq4 S N c form
  toOriginal := back

abbrev data := A.data G (anchor G L F S back N c nonzero form)

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient L S⊆
    GenericOrdinarySource.family G (data G L F S back N c nonzero form) :=
  A.old_included G (anchor G L F S back N c nonzero form)

variable (z : Fin r)
variable (zLiteral : (⟨b z.val,S z⟩ : AnySignature L)=⟨2,NoXGeneralZSign.signature⟩)

include zLiteral in
theorem z_member : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈
    GenericOrdinarySource.family G (data G L F S back N c nonzero form) := by
  apply old_included G L F S back N c nonzero form
  refine ⟨z,?_⟩
  change RingHomRealization.mapAny L.subtype (⟨b z.val,S z⟩ : AnySignature L)=_
  rw [zLiteral]
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,NoXGeneralZSign.signature,zAnchor,kernelSignature,diagonalKernel,h0,h1]

include back nonzero form zLiteral in
theorem classified : Tract (GlobalCloseCompletionUnaryDescentSource.ambient L S) ∨
    NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  let src:=data G L F S back N c nonzero form
  by_cases positive : Tract (GenericOrdinarySource.family G src)
  · exact Or.inl (positive.mono_family (old_included G L F S back N c nonzero form))
  · right
    obtain ⟨j,literal⟩:=GlobalCloseCompletionUnaryIsotropicLift.z_exists src.K src.H
      (z_member G L F S back N c nonzero form z zLiteral)
    have exactZ : (⟨src.b j.val,src.H j⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩ := by
      refine literal.trans ?_
      apply congrArg (fun f : Signature src.K 2=>(⟨2,f⟩ : AnySignature src.K))
      funext x
      cases x 0 <;> cases x 1 <;> rfl
    exact NoXGeneralComplete.countingHard G src j exactZ ((GenericOrdinarySource.rejected_iff G src).mp positive)

include back nonzero form in
theorem classified_x (j : Fin r)
    (literal : (⟨b j.val,S j⟩ : AnySignature L)=⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩) :
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient L S) ∨
      NoXWeightedAntiResourcesOriginal.Hard G :=
  GlobalCloseCompletionC2OrdinaryAnchorX.classified G (anchor G L F S back N c nonzero form) j literal


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZEquality
end
