import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportWitness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGadgetRecipe
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSignedBinarySource

/-! Nonclosed support of any actual even private trace gives a counted-verifier
source through its internally selected support shift and fixed three-support
gadget. The private block can have arbitrary exposed and private arities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportEvenSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace D
export OrdinaryNegativeMixedBlockData (Recipe Node coefficient ports EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace W
export OrdinaryNegativeNonclosedSupportWitness (Choice choose nonaffine nonproduct)
end W
namespace E
export OrdinaryNegativeAffineSupportExtraction (shift)
end E
namespace G
export OrdinaryNegativeAffineSupportGadgetRecipe (recipe privateCount even_recipe trace_eq)
end G
namespace X
export OrdinaryNegativeMixedBlockSigned (recipe even_recipe trace_value)
end X
namespace S
export OrdinaryNegativeMixedBlockSignedBinarySource (source binary)
end S
namespace C
export GeneralEONegativeClosedSupport (Closed)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {d s n k : ℕ} {b : ℕ→ℕ}
variable (F : FixedField K d) (H : (i : Fin s)→Signature K (b i.val))
variable (resource : D.Recipe (u:=1) (s:=s) (a:=fun _=>n+k) (b:=b))
variable (nonclosed : ¬C.Closed (fun x=>(D.trace H k resource 0 x : AlgebraicComplex)))

include nonclosed in
theorem resource_nonclosed : ¬∀a c e,
    D.trace H k resource 0 a≠0→D.trace H k resource 0 c≠0→
    D.trace H k resource 0 e≠0→D.trace H k resource 0 (tripleXor a c e)≠0 := by
  intro hh
  apply nonclosed
  intro a c e ha hc he
  have hne (x : Fin n→Bool) (hx : (D.trace H k resource 0 x : AlgebraicComplex)≠0) :
      D.trace H k resource 0 x≠0 :=
    fun hz=>hx (congrArg (fun v : K=>(v : AlgebraicComplex)) hz)
  intro hz
  exact hh a c e (hne a ha) (hne c hc) (hne e he) (Subtype.ext hz)

def choice : W.Choice (D.trace H k resource 0) :=
  W.choose _ (resource_nonclosed K H resource nonclosed)

variable (xLabel p0 : Fin s)
variable (hx : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=
  ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)

def shifted := X.recipe resource (fun _ : Fin 1=>(choice K H resource nonclosed).base)
  xLabel p0 (congrArg Sigma.fst hx) (congrArg Sigma.fst h0)

abbrev privateCount := G.privateCount (k:=n+k) (choice K H resource nonclosed).gadget

def blocks := G.recipe (choice K H resource nonclosed).gadget
  (shifted K H resource nonclosed xLabel p0 hx h0)

theorem balanced (evenResource : D.EvenRecipe resource) : D.EvenRecipe (blocks K H resource nonclosed xLabel p0 hx h0) :=
  G.even_recipe _ _ (X.even_recipe _ _ _ _ _ _ evenResource)

theorem binary_exact :
    D.trace H (privateCount K H resource nonclosed)
      (blocks K H resource nonclosed xLabel p0 hx h0) 0=(choice K H resource nonclosed).coefficient := by
  funext z
  rw [blocks,G.trace_eq]
  have hrow : D.trace H (n+k) (shifted K H resource nonclosed xLabel p0 hx h0) 0=
      E.shift (D.trace H k resource 0) (choice K H resource nonclosed).base := by
    funext x
    exact X.trace_value _ _ xLabel p0 H hx h0 0 x
  rw [hrow]
  rfl

theorem binary_nonaffine :
    ¬Affine (GeneralEOBinaryLiftOriginalField.complexRow K
      (S.binary K H (blocks K H resource nonclosed xLabel p0 hx h0))) := by
  change ¬Affine (fun z=>((D.trace H (privateCount K H resource nonclosed)
    (blocks K H resource nonclosed xLabel p0 hx h0) 0 z : K) : AlgebraicComplex))
  rw [binary_exact]
  exact W.nonaffine K _ (choice K H resource nonclosed).three

theorem binary_nonproduct :
    ¬Product (GeneralEOBinaryLiftOriginalField.complexRow K
      (S.binary K H (blocks K H resource nonclosed xLabel p0 hx h0))) := by
  change ¬Product (fun z=>((D.trace H (privateCount K H resource nonclosed)
    (blocks K H resource nonclosed xLabel p0 hx h0) 0 z : K) : AlgebraicComplex))
  rw [binary_exact]
  exact W.nonproduct K _ (choice K H resource nonclosed).three

variable (e p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- Actual even resource, support nonclosure, and literal Eq4/pins/X suffice. -/
def source (evenResource : D.EvenRecipe resource) (w : SharpPWitness ea count) :=
  S.source K F H e p0 p1 xLabel he h0 h1 hx
    (blocks K H resource nonclosed xLabel p0 hx h0)
    (balanced K H resource nonclosed xLabel p0 hx h0 evenResource)
    (binary_nonaffine K H resource nonclosed xLabel p0 hx h0)
    (binary_nonproduct K H resource nonclosed xLabel p0 hx h0) w

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportEvenSource
end
