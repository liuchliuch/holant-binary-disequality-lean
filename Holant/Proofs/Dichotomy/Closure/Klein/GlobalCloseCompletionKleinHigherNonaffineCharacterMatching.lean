import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCurrent
import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedCharacterLeaf
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterCurrentResources

/-! Every actual standard-Pauli matching is character-flat, with arbitrary
matching size, original port order and scalar retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCharacterMatching
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
open scoped BigOperators
namespace P
export GlobalCloseCompletionKleinHigherNonaffine (Label E EOver xLabel yLabel zLabel label_cases Matching)
export GlobalCloseCompletionKleinHigherNonaffine.MatchingCard (PauliMatchingOrZero)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def twoBool : Fin 2 ≃ Bool where
  toFun := ![false,true]
  invFun := fun b=>if b then 1 else 0
  left_inv := by decide
  right_inv := by decide

theorem E_bell (a : P.Label) : (fun x : Fin 2→Bool=>P.E a (x 0) (x 1))=bellSignature a.2 a.1 := by
  funext x
  rcases P.label_cases a with rfl|rfl|rfl|rfl <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [P.E,P.EOver,P.xLabel,P.yLabel,P.zLabel,bellSignature,bellKernel,
      sign,intSign,bit,boolEquiv,parityKernel,h0,h1]
  all_goals decide

theorem E_character (a : P.Label) : CFlat (fun x : Fin 2→Bool=>P.E a (x 0) (x 1)) := by
  rw [E_bell]
  exact Or.inr (bellSignature_nonzeroFlat _ _)

theorem matching_character {n r : ℕ} (M : P.Matching (Fin n) r) (labels : Fin r→P.Label) :
    CFlat (M.tensor labels) := by
  let factors : (e : Fin r)→Signature ℂ 2 := fun e x=>P.E (labels e) (x 0) (x 1)
  let ports : (Σ _ : Fin r,Fin 2)≃Fin n :=
    (Equiv.sigmaEquivProd (Fin r) (Fin 2)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin r)) twoBool).trans M.ports)
  have product := vertexProduct_CFlat factors (fun e=>E_character (labels e))
  have moved := product.reindex ports
  have value : Tensor.reindex ports (vertexProduct factors)=M.tensor labels := by
    funext x
    simp [Tensor.reindex,vertexProduct,factors,ports,twoBool,
      GlobalCloseCompletionKleinHigherNonaffine.Matching.tensor]
  rw [value] at moved
  exact (characterTensorOrZero_fin_iff _).mp moved

theorem pauli_character {n : ℕ} (f : Signature ℂ n) (matching : P.PauliMatchingOrZero f) : CFlat f := by
  rcases matching with rfl|⟨r,M,labels,c,_live,rfl⟩
  · exact Or.inl rfl
  · exact (matching_character M labels).smul _ c

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (palette : Palette G) (torsion : ResidualTorsion palette.family)
variable (cardinal : Nat.card (completeGroup palette.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup palette.family torsion))
variable (standard : ClosureKleinCurrent.kind G palette torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard in
theorem current_matching_character {n : ℕ} (f : Signature (OI.K G) n)
    (matching : MatchingOrZero (actualTransfers palette.family) f) :
    CFlat (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f) := by
  have h := ClosureKleinCurrent.matching_mapped G palette torsion cardinal noncyclic f matching
  rw [standard] at h
  exact pauli_character _ (GlobalCloseCompletionKleinHigherNonaffineCurrent.canonical_pauli _ h)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCharacterMatching
end
