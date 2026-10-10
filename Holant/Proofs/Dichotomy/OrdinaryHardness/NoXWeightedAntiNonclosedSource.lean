import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportWitness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGadgetRecipe
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiBinarySource

/-! Nonclosed support of any actual even private trace gives a counted-verifier
source through its internally selected support shift and fixed three-support
gadget. The private block can have arbitrary exposed and private arities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiNonclosedSource
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
export NoXWeightedAntiSigned (recipe even_recipe trace_value)
end X
namespace S
export NoXWeightedAntiBinarySource (source binary)
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

variable (antiLabel : Fin s) (v w : K)
variable (hv : v≠0) (hw : w≠0)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)

def shifted := X.recipe resource (fun _ : Fin 1=>(choice K H resource nonclosed).base)
  antiLabel (congrArg Sigma.fst ha_lit)

abbrev privateCount := G.privateCount (k:=n+k) (choice K H resource nonclosed).gadget

def blocks := G.recipe (choice K H resource nonclosed).gadget
  (shifted K H resource nonclosed antiLabel v w ha_lit)

theorem balanced (evenResource : D.EvenRecipe resource) : D.EvenRecipe (blocks K H resource nonclosed antiLabel v w ha_lit) :=
  G.even_recipe _ _ (X.even_recipe _ _ _ _ evenResource)

theorem binary_exact :
    D.trace H (privateCount K H resource nonclosed)
      (blocks K H resource nonclosed antiLabel v w ha_lit) 0=fun z=>((v*w)^n)^(choice K H resource nonclosed).gadget.ports.length*
        (choice K H resource nonclosed).coefficient z := by
  funext z
  rw [blocks,G.trace_eq]
  have hrow : D.trace H (n+k) (shifted K H resource nonclosed antiLabel v w ha_lit) 0=
      (fun x=>(v*w)^n*E.shift (D.trace H k resource 0) (choice K H resource nonclosed).base x) := by
    funext x
    exact X.trace_value _ _ antiLabel H v w ha_lit 0 x
  rw [hrow,NoXScaleAux.gadget_scale]
  rfl

include hv hw in
theorem binary_nonaffine :
    ¬Affine (GeneralEOBinaryLiftOriginalField.complexRow K
      (D.trace H (privateCount K H resource nonclosed)
        (blocks K H resource nonclosed antiLabel v w ha_lit) 0)) := by
  rw [binary_exact]
  exact NoXScaleAux.nonaffine_scale _ (W.nonaffine K _ (choice K H resource nonclosed).three)
    _ (fun hz=> (pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))

include hv hw in
theorem binary_nonproduct :
    ¬Product (GeneralEOBinaryLiftOriginalField.complexRow K
      (D.trace H (privateCount K H resource nonclosed)
        (blocks K H resource nonclosed antiLabel v w ha_lit) 0)) := by
  rw [binary_exact]
  exact NoXScaleAux.nonproduct_scale _ (W.nonproduct K _ (choice K H resource nonclosed).three)
    _ (fun hz=> (pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))

variable (e p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- Actual even resource, support nonclosure, and literal Eq4/pins and a full weighted antidiagonal suffice. -/
def source (evenResource : D.EvenRecipe resource) (witness : SharpPWitness ea count) :=
  S.source K F H e p0 p1 antiLabel he h0 h1 v w hv hw ha_lit
    (blocks K H resource nonclosed antiLabel v w ha_lit)
    (balanced K H resource nonclosed antiLabel v w ha_lit evenResource)
    (binary_nonaffine K H resource nonclosed antiLabel v w hv hw ha_lit)
    (binary_nonproduct K H resource nonclosed antiLabel v w hv hw ha_lit) witness

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiNonclosedSource
end
