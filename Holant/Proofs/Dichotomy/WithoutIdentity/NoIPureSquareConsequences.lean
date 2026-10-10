import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportEvenSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSource
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness

/-! Exact algebraic consequences of an ordinary squared-table source retaining
Eq4, both pins and X. The negative alternatives carry actual counted-verifier
programmes in the exact table codec. No common-basis support shortcut is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareConsequences
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport (Closed)
end C
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace N
export OrdinaryNegativeNonproductBundleChoice (Choice choose duplicate duplicate_even duplicate_value)
export OrdinaryNegativeNonproductBundleSource (recipe even_recipe coefficient_eq)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (H : (i : Fin size)→Signature L (arity i.val)) (F : FixedField L degree)
variable (e p0 p1 x : Fin size)
variable (he : (⟨arity e.val,H e⟩ : AnySignature L)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : (⟨arity p0.val,H p0⟩ : AnySignature L)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h1 : (⟨arity p1.val,H p1⟩ : AnySignature L)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (hx : (⟨arity x.val,H x⟩ : AnySignature L)=⟨2,fun z=>Signature.disequality (z 0) (z 1)⟩)

def target : NoIOrdinaryRaw.Target:=PaperControlledHardness.target
  (RawClosedNetwork.validatedEncoding size 1 arity) F.encoding
  ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}
def nonclosedSource (j : Fin size) (bad : ¬C.Closed (fun z=>(H j z : AlgebraicComplex)))
    (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
      (target L H F).inputEncoding (target L H F).outputEncoding f (target L H F).value:=
  OrdinaryNegativeNonclosedSupportSource.source L F H j bad x p0 hx h0 e p1 he h1 w

include he h0 h1 hx in
theorem support_or_hard : (∀j,C.Closed (fun z=>(H j z : AlgebraicComplex))) ∨ (target L H F).Hard := by
  classical
  by_cases all : ∀j,C.Closed (fun z=>(H j z : AlgebraicComplex))
  · exact Or.inl all
  · right
    obtain ⟨j,bad⟩:=not_forall.mp all
    intro α ea f w
    exact ⟨nonclosedSource L H F e p0 p1 x he h0 h1 hx j bad w⟩

variable {m n k l : ℕ}
def resourcesSource
    (first : D.Recipe (u:=1) (s:=size) (a:=fun _=>m+k) (b:=arity))
    (second : D.Recipe (u:=1) (s:=size) (a:=fun _=>n+l) (b:=arity))
    (badA : ¬Affine (fun z=>(D.trace H k first 0 z : AlgebraicComplex)))
    (badP : ¬Product (fun z=>(D.trace H l second 0 z : AlgebraicComplex)))
    (evenA : D.EvenRecipe first) (evenP : D.EvenRecipe second) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool
      (target L H F).inputEncoding (target L H F).outputEncoding f (target L H F).value := by
  classical
  by_cases ca : C.Closed (fun z=>(D.trace H k first 0 z : AlgebraicComplex))
  · by_cases cp : C.Closed (fun z=>(D.trace H l second 0 z : AlgebraicComplex))
    · exact OrdinaryNegativeAffineSupportSource.source L F H first second ca cp badA badP
        x p0 hx h0 e p1 he h1 evenA evenP w
    · exact OrdinaryNegativeNonclosedSupportEvenSource.source L F H second cp x p0 hx h0 e p1 he h1 evenP w
  · exact OrdinaryNegativeNonclosedSupportEvenSource.source L F H first ca x p0 hx h0 e p1 he h1 evenA w

/-- Fixed positive recipes retain their original source coefficients. -/
theorem recipe_trace (j : Fin size) (ps : List (Fin (arity j.val)→Bool ⊕ Fin (arity j.val)))
    (z : Fin (arity j.val)→Bool) : D.trace H 0 (N.recipe j ps) 0 z=
      Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle.evaluate (H j) ps z := by
  have word (y : Fin 0→Bool) : Fin.addCases (m:=arity j.val) (n:=0) z y=z:=by
    funext i
    exact Fin.addCases_left i
  change (∑y : Fin 0→Bool,OrdinaryNegativeMixedBlockData.coefficient H (N.recipe j ps) 0 (Fin.addCases (m:=arity j.val) (n:=0) z y))=_
  simp_rw [word]
  simp only [N.coefficient_eq,Fintype.sum_unique]

include he h0 h1 hx in
/-- Either every pointwise square is literally Affine, or every original row
is literally Product, or the exact whole ordinary table is controlled hard. -/
theorem magnitude_or_hard :
    (∀j,Affine (fun z=>(H j z : AlgebraicComplex)^2)) ∨
    (∀j,Product (fun z=>(H j z : AlgebraicComplex))) ∨ (target L H F).Hard := by
  classical
  by_cases allA : ∀j,Affine (fun z=>(H j z : AlgebraicComplex)^2)
  · exact Or.inl allA
  by_cases allP : ∀j,Product (fun z=>(H j z : AlgebraicComplex))
  · exact Or.inr (Or.inl allP)
  right;right
  obtain ⟨j,badA⟩:=not_forall.mp allA
  obtain ⟨q,badP⟩:=not_forall.mp allP
  let bundle:=N.choose L (H q) badP
  have first : ¬Affine (fun z=>(D.trace H 0 (N.recipe j N.duplicate) 0 z : AlgebraicComplex)) := by
    have value (z : Fin (arity j.val)→Bool) :
        (D.trace H 0 (N.recipe j N.duplicate) 0 z : AlgebraicComplex)=(H j z : AlgebraicComplex)^2 := by
      rw [recipe_trace,N.duplicate_value]
      exact map_pow L.val.toRingHom _ 2
    simpa only [value] using badA
  have second : ¬Product (fun z=>(D.trace H 0 (N.recipe q bundle.rows) 0 z : AlgebraicComplex)) := by
    simpa only [recipe_trace] using bundle.nonproduct
  intro α ea f w
  exact ⟨resourcesSource L H F e p0 p1 x he h0 h1 hx _ _ first second
    (N.even_recipe j N.duplicate N.duplicate_even) (N.even_recipe q bundle.rows bundle.even) w⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareConsequences
end
