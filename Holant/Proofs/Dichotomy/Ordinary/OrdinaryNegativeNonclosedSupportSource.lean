import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonclosedSupportWitness
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportGadgetRecipe
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSignedBinarySource

/-! An original ordinary row with non-affine support directly supplies a
counting source. Squaring only regularizes occurrence parity, literal X realizes
the internally selected support shift, and the fixed three-support gadget is
flattened with all original labels and private sums intact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportSource
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
variable {d s : ℕ} {b : ℕ→ℕ}
variable (F : FixedField K d) (H : (i : Fin s)→Signature K (b i.val))
variable (label : Fin s)
variable (nonclosed : ¬C.Closed (fun x=>(H label x : AlgebraicComplex)))

/-- Exactly two copies of the selected original row. -/
def squareRecipe : D.Recipe (u:=1) (s:=s) (a:=fun _=>b label.val+0) (b:=b) :=
  fun _=>[⟨label,fun i=>.inr i⟩,⟨label,fun i=>.inr i⟩]

theorem square_even : D.EvenRecipe (squareRecipe (b:=b) label) := by
  intro i p
  simp only [D.ports,squareRecipe,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
  exact ⟨_,rfl⟩

theorem square_trace (z : Fin (b label.val)→Bool) :
    D.trace H 0 (squareRecipe (b:=b) label) 0 z=H label z^2 := by
  unfold D.trace D.coefficient GeneralEOPairedFamilyBundleValue.coefficient squareRecipe
  simp only [Fintype.sum_unique,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Sum.elim_inr]
  change H label (fun i : Fin (b label.val)=>Fin.addCases z (_ : Fin 0→Bool) i)*
    H label (fun i : Fin (b label.val)=>Fin.addCases z (_ : Fin 0→Bool) i)=H label z^2
  have he (y : Fin 0→Bool) : (fun i : Fin (b label.val)=>Fin.addCases z y i)=z := by
    funext i
    exact Fin.addCases_left i
  simp only [he,pow_two]

include nonclosed in
theorem square_nonclosed : ¬∀a c e,
    D.trace H 0 (squareRecipe (b:=b) label) 0 a≠0→
    D.trace H 0 (squareRecipe (b:=b) label) 0 c≠0→
    D.trace H 0 (squareRecipe (b:=b) label) 0 e≠0→
    D.trace H 0 (squareRecipe (b:=b) label) 0 (tripleXor a c e)≠0 := by
  intro hh
  apply nonclosed
  intro a c e ha hc he
  have hne (x : Fin (b label.val)→Bool) (hx : (H label x : AlgebraicComplex)≠0) : H label x≠0 :=
    fun hz=>hx (congrArg (fun v : K=>(v : AlgebraicComplex)) hz)
  have h := hh a c e (by rw [square_trace]; exact pow_ne_zero 2 (hne a ha))
    (by rw [square_trace]; exact pow_ne_zero 2 (hne c hc))
    (by rw [square_trace]; exact pow_ne_zero 2 (hne e he))
  intro hz
  apply h
  rw [square_trace,show H label (tripleXor a c e)=0 from Subtype.ext hz]
  norm_num

def choice : W.Choice (D.trace H 0 (squareRecipe (b:=b) label) 0) :=
  W.choose _ (square_nonclosed K H label nonclosed)

variable (xLabel p0 : Fin s)
variable (hx : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=
  ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)

def shifted := X.recipe (squareRecipe (b:=b) label) (fun _ : Fin 1=>(choice K H label nonclosed).base)
  xLabel p0 (congrArg Sigma.fst hx) (congrArg Sigma.fst h0)

abbrev privateCount := G.privateCount (k:=b label.val+0) (choice K H label nonclosed).gadget

def blocks := G.recipe (choice K H label nonclosed).gadget
  (shifted K H label nonclosed xLabel p0 hx h0)

theorem balanced : D.EvenRecipe (blocks K H label nonclosed xLabel p0 hx h0) :=
  G.even_recipe _ _ (X.even_recipe _ _ _ _ _ _ (square_even label))

theorem binary_exact :
    D.trace H (privateCount K H label nonclosed)
      (blocks K H label nonclosed xLabel p0 hx h0) 0=(choice K H label nonclosed).coefficient := by
  funext z
  rw [blocks,G.trace_eq]
  have hrow : D.trace H (b label.val+0) (shifted K H label nonclosed xLabel p0 hx h0) 0=
      E.shift (D.trace H 0 (squareRecipe (b:=b) label) 0) (choice K H label nonclosed).base := by
    funext x
    exact X.trace_value _ _ xLabel p0 H hx h0 0 x
  rw [hrow]
  rfl

theorem binary_nonaffine :
    ¬Affine (GeneralEOBinaryLiftOriginalField.complexRow K
      (S.binary K H (blocks K H label nonclosed xLabel p0 hx h0))) := by
  change ¬Affine (fun z=>((D.trace H (privateCount K H label nonclosed)
    (blocks K H label nonclosed xLabel p0 hx h0) 0 z : K) : AlgebraicComplex))
  rw [binary_exact]
  exact W.nonaffine K _ (choice K H label nonclosed).three

theorem binary_nonproduct :
    ¬Product (GeneralEOBinaryLiftOriginalField.complexRow K
      (S.binary K H (blocks K H label nonclosed xLabel p0 hx h0))) := by
  change ¬Product (fun z=>((D.trace H (privateCount K H label nonclosed)
    (blocks K H label nonclosed xLabel p0 hx h0) 0 z : K) : AlgebraicComplex))
  rw [binary_exact]
  exact W.nonproduct K _ (choice K H label nonclosed).three

variable (e p1 : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}

/-- Original row, support nonclosure, and literal Eq4/pins/X suffice. -/
def source (w : SharpPWitness ea count) :=
  S.source K F H e p0 p1 xLabel he h0 h1 hx
    (blocks K H label nonclosed xLabel p0 hx h0)
    (balanced K H label nonclosed xLabel p0 hx h0)
    (binary_nonaffine K H label nonclosed xLabel p0 hx h0)
    (binary_nonproduct K H label nonclosed xLabel p0 hx h0) w

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonclosedSupportSource
end
