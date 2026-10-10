import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleChoice
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource

/-! Physical ordinary-CSP source for the internally regularized non-Product
row. The source is unrestricted in variable degree; its fixed literal recipe
makes every target variable even before the ordinary compiler is invoked. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
namespace D
export OrdinaryNegativeMixedBlockData (Recipe Node EvenRecipe coefficient family inputEncoding Input)
end D
namespace M
export OrdinaryNegativeMixedBlockSource (controlled value)
end M
namespace B
export GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace O
export GeneralEOPairedFamilyExtractionPhaseOccurrences (rawPorts)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {b : ℕ→ℕ}
variable (j : Fin s) (ps : List (Fin (b j.val)→Bool ⊕ Fin (b j.val)))

/-- Every emitted node uses exactly the original selected label. -/
def recipe : D.Recipe (u:=1) (s:=s) (a:=fun _=>b j.val) (b:=b) :=
  fun _=>ps.map (fun p=>⟨j,p⟩)

theorem ports_eq (i : Fin 1) :
    OrdinaryNegativeMixedBlockData.ports (recipe j ps) i=O.rawPorts ps := by
  simp only [OrdinaryNegativeMixedBlockData.ports,recipe,List.flatMap_map,O.rawPorts]
  rfl

theorem even_recipe (he : ∀q : Bool ⊕ Fin (b j.val),Even ((O.rawPorts ps).count q)) :
    D.EvenRecipe (recipe j ps) := by
  intro i q
  rw [ports_eq]
  exact he q

variable {K : Type} [Field K] (H : (i : Fin s)→Signature K (b i.val))

theorem coefficient_eq (i : Fin 1) (x : Fin (b j.val)→Bool) :
    D.coefficient H (recipe j ps) i x=B.evaluate (H j) ps x := by
  simp only [D.coefficient,GeneralEOPairedFamilyBundleValue.coefficient,recipe,List.map_map,
    Function.comp_def,B.evaluate]
  rfl

section Source
variable [Algebra ℚ K] {d : ℕ} (F : FixedField K d)
variable (e p₀ p₁ : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (balanced : ∀q : Bool ⊕ Fin (b j.val),Even ((O.rawPorts ps).count q))

def controlled : LengthControlledOracleReduction
    (D.inputEncoding (u:=1) (a:=fun _=>b j.val)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding
    (M.value H (recipe j ps)) ((StableHigherCurrentEvenCSPSource.tables F H).evaluate F) :=
  M.controlled F H (recipe j ps) e p₀ p₁ he h₀ h₁ (even_recipe j ps balanced)

end Source
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeNonproductBundleSource
end
