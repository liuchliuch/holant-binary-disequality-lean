import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGadgetRecipe
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiBinarySource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiTensor

/-! Actual counted-verifier source from two even ordinary resources with affine
supports and incompatible A/P membership. Tensor, support shifts, extracted
binary gadget, every private block, oppositely oriented weighted antidiagonal rows, and the original-field
binary hardness programme are all constructed here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiAffineSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace E
export OrdinaryNegativeAffineSupportExtraction (Choice choose ambientLeft ambientRight combined)
end E
namespace T
export NoXWeightedAntiTensor (shiftedRecipe shifted_even shifted_trace)
end T
namespace G
export OrdinaryNegativeAffineSupportGadgetRecipe (recipe privateCount even_recipe trace_eq)
end G
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
variable {d s m n k l : ℕ} {b : ℕ→ℕ}
variable (F : FixedField K d) (H : (i : Fin s)→Signature K (b i.val))
variable (first : D.Recipe (u:=1) (s:=s) (a:=fun _=>m+k) (b:=b))
variable (second : D.Recipe (u:=1) (s:=s) (a:=fun _=>n+l) (b:=b))
variable (hf : C.Closed (fun x=>((D.trace H k first 0 x : K) : AlgebraicComplex)))
variable (hg : C.Closed (fun x=>((D.trace H l second 0 x : K) : AlgebraicComplex)))
variable (ha : ¬Affine (fun x=>((D.trace H k first 0 x : K) : AlgebraicComplex)))
variable (hp : ¬Product (fun x=>((D.trace H l second 0 x : K) : AlgebraicComplex)))

def choice : E.Choice K (D.trace H k first 0) (D.trace H l second 0) :=
  E.choose K _ _ hf hg ha hp

variable (antiLabel : Fin s) (v w : K)
variable (hv : v≠0) (hw : w≠0)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=
  ⟨2,NoXWeightedAntiSigned.anti v w⟩)

def shifted := T.shiftedRecipe first second (choice K H first second hf hg ha hp).left
  (choice K H first second hf hg ha hp).right antiLabel (congrArg Sigma.fst ha_lit)

abbrev privateCount := G.privateCount (k:=(m+n)+(k+l)) (choice K H first second hf hg ha hp).gadget

def blocks := G.recipe (choice K H first second hf hg ha hp).gadget
  (shifted K H first second hf hg ha hp antiLabel v w ha_lit)

theorem balanced (hfirst : D.EvenRecipe first) (hsecond : D.EvenRecipe second) :
    D.EvenRecipe (blocks K H first second hf hg ha hp antiLabel v w ha_lit) :=
  G.even_recipe _ _ (T.shifted_even first second _ _ antiLabel
    (congrArg Sigma.fst ha_lit) hfirst hsecond)

theorem binary_exact :
    D.trace H (privateCount K H first second hf hg ha hp)
      (blocks K H first second hf hg ha hp antiLabel v w ha_lit) 0=
        fun z=>((v*w)^(m+n))^(choice K H first second hf hg ha hp).gadget.ports.length*
          (choice K H first second hf hg ha hp).coefficient z := by
  funext z
  rw [blocks,G.trace_eq]
  have hrow : D.trace H ((m+n)+(k+l)) (shifted K H first second hf hg ha hp antiLabel v w ha_lit) 0=
      (fun x=>(v*w)^(m+n)*E.combined (D.trace H k first 0) (D.trace H l second 0)
        (choice K H first second hf hg ha hp).left (choice K H first second hf hg ha hp).right x) := by
    funext x
    exact T.shifted_trace first second _ _ antiLabel H v w ha_lit x
  rw [hrow,NoXScaleAux.gadget_scale]
  rfl

include hv hw in
theorem binary_nonaffine :
    ¬Affine (GeneralEOBinaryLiftOriginalField.complexRow K
      (D.trace H (privateCount K H first second hf hg ha hp)
        (blocks K H first second hf hg ha hp antiLabel v w ha_lit) 0)) := by
  rw [binary_exact]
  exact NoXScaleAux.nonaffine_scale _ (choice K H first second hf hg ha hp).nonaffine
    _ (fun hz=> (pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))

include hv hw in
theorem binary_nonproduct :
    ¬Product (GeneralEOBinaryLiftOriginalField.complexRow K
      (D.trace H (privateCount K H first second hf hg ha hp)
        (blocks K H first second hf hg ha hp antiLabel v w ha_lit) 0)) := by
  rw [binary_exact]
  exact NoXScaleAux.nonproduct_scale _ (choice K H first second hf hg ha hp).nonproduct
    _ (fun hz=> (pow_ne_zero _ (pow_ne_zero _ (mul_ne_zero hv hw))) (Subtype.ext hz))

variable (e p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (hfirst : D.EvenRecipe first) (hsecond : D.EvenRecipe second)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- All combinatorial and counting resources are constructed from the two
actual even blocks and the target table's literal Eq4, pins, and a full weighted antidiagonal. -/
def source (witness : SharpPWitness ea count) :=
  S.source K F H e p0 p1 antiLabel he h0 h1 v w hv hw ha_lit
    (blocks K H first second hf hg ha hp antiLabel v w ha_lit)
    (balanced K H first second hf hg ha hp antiLabel v w ha_lit hfirst hsecond)
    (binary_nonaffine K H first second hf hg ha hp antiLabel v w hv hw ha_lit)
    (binary_nonproduct K H first second hf hg ha hp antiLabel v w hv hw ha_lit) witness

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiAffineSource
end
