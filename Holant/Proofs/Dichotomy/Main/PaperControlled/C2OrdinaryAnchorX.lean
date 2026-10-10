import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal

/-! An actual scalar-Eq4 graph and a retained literal-X row in the same
ordinary dictionary give the full unchanged-source alternative. The literal
X row is recovered across the anchor programme's actual coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryAnchorX
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace I
export GlobalCloseCompletionOrdinaryAnchorInput (Input mapped)
end I
namespace P
export GlobalCloseCompletionOrdinaryAnchorPins (data old_included antiRow)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val)) (D : I.Input G)
local instance : Algebra ℚ D.K := D.K.algebra'
variable (j : Fin D.count)
variable (literal : (⟨D.b j.val,D.H j⟩ : AnySignature D.K)=
  ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)

private theorem anti_one : NoXWeightedAntiSigned.anti (1:D.K) 1=
    fun x=>Signature.disequality (x 0) (x 1) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [NoXWeightedAntiSigned.anti,Signature.disequality,h0,h1]

def row := P.antiRow G D 1 1 j (literal.trans
  (congrArg (fun f : Signature D.K 2=>(⟨2,f⟩ : AnySignature D.K)) (anti_one G D).symm))

def data : GenericLiteralXSource.Data G where
  K := (P.data G D).K
  degree := (P.data G D).degree
  F := (P.data G D).F
  size := (P.data G D).size
  b := (P.data G D).b
  H := (P.data G D).H
  e := (P.data G D).e
  p := (P.data G D).p
  x := (row G D j literal).label
  he := (P.data G D).he
  hp := (P.data G D).hp
  hx := by
    have vl : (row G D j literal).left=1 := Subtype.ext ((row G D j literal).left_value)
    have vr : (row G D j literal).right=1 := Subtype.ext ((row G D j literal).right_value)
    have h := (row G D j literal).literal
    rw [vl,vr] at h
    refine h.trans ?_
    apply congrArg (fun f : Signature (P.data G D).K 2=>(⟨2,f⟩ : AnySignature (P.data G D).K))
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [NoXWeightedAntiSigned.anti,Signature.disequality,h0,h1]
  toOriginal := (P.data G D).toOriginal

theorem old_included : UniversalPairReduction.FiniteFamily.family (I.mapped G D)⊆
    GenericLiteralXSource.family G (data G D j literal) := P.old_included G D

include j literal in
theorem classified : Tract (UniversalPairReduction.FiniteFamily.family (I.mapped G D)) ∨
    PaperControlledHardness.Hard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
      (OriginalForestSource.value G) := by
  rcases PaperControlledOrdinary.literalX_classified G (data G D j literal) with tract|hard
  · exact Or.inl (tract.mono_family (old_included G D j literal))
  · exact Or.inr hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryAnchorX
end
