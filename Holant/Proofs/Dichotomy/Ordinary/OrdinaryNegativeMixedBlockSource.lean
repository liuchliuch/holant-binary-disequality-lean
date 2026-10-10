import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockProgramme
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockValidity
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSemantics
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentEvenCSPSource

/-! Actual ordinary finite-family block composition, including private
variables. The old mixed CSP writers supply only literal records and exact
finite sums. The target is the actual ordinary table with Eq4 and both pins;
no signed CSP oracle or EO covering promise is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace C
export GeneralEOPairedCSPFamilyRaw (value)
end C
namespace W
export GeneralEOPairedFamilyPrivateRaw (query queryComputes)
export GeneralEOPairedFamilyPrivateValue (query_valid query_value trace)
end W
namespace E
export StableHigherCurrentEvenCSPSource (controlled tables)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

variable {K : Type} [Field K] [Algebra ℚ K] {d u s : ℕ} {a b : ℕ→ℕ}
variable (F : FixedField K d) (H : (j : Fin s)→Signature K (b j.val))
variable (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b))
variable (e p₀ p₁ : Fin s)
variable (he : (⟨b e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h₀ : (⟨b p₀.val,H p₀⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)
variable (h₁ : (⟨b p₁.val,H p₁⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin true⟩)
variable (even : EvenRecipe recipe)

abbrev query := OrdinaryNegativeMixedBlockValidity.query recipe p₀ p₁
  (congrArg Sigma.fst h₀) (congrArg Sigma.fst h₁) even

def queryComputes : Computes (OrdinaryNegativeMixedBlockData.inputEncoding (u:=u) (a:=a))
    (Raw.validatedEncoding s b) (query H recipe p₀ p₁ h₀ h₁ even) :=
  recode (OrdinaryNegativeMixedBlockProgramme.rawComputes recipe p₀ p₁) Subtype.val
    (fun _=>rfl) (fun _=>rfl)

abbrev value (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) : K :=
  C.value (s:=u) (arity:=fun i=>a i*2) (family u a) (coefficient H recipe) r.val

omit [Algebra ℚ K] in
theorem query_value (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) :
    Raw.value H (query H recipe p₀ p₁ h₀ h₁ even r)=value H recipe r := by
  rw [StableHigherCurrentOrdinarySquare.typed_value]
  exact OrdinaryNegativeMixedBlockSemantics.value H recipe p₀ p₁ h₀ h₁ r

def bundleControlled : LengthControlledOracleReduction
    (OrdinaryNegativeMixedBlockData.inputEncoding (u:=u) (a:=a)) F.encoding
    (Raw.validatedEncoding s b) F.encoding (value H recipe) (Raw.value H) :=
  controlledOneQueryOfEq (queryComputes H recipe p₀ p₁ h₀ h₁ even)
    (identityComputes F.encoding) (E.controlled F H e he).sourceOutputBound
    (value H recipe) (fun r=>(query_value H recipe p₀ p₁ h₀ h₁ even r).symm)

def controlled : LengthControlledOracleReduction
    (OrdinaryNegativeMixedBlockData.inputEncoding (u:=u) (a:=a)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding (value H recipe)
    ((E.tables F H).evaluate F) :=
  Programme.compose (bundleControlled F H recipe e p₀ p₁ he h₀ h₁ even)
    (E.controlled F H e he)

section Private
variable (k : ℕ)
variable (blocks : Recipe (u:=u) (s:=s) (a:=fun i=>a i+k) (b:=b))
variable (balanced : EvenRecipe blocks)

def privateQuery (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) :
    OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=fun i=>a i+k) :=
  ⟨W.query (s:=u) (a:=fun i=>a i*2) (b:=fun i=>(a i+k)*2)
    (family u a) (family u (fun i=>a i+k)) k (fun _=>rfl) r.val,
    W.query_valid (s:=u) (a:=fun i=>a i*2) (b:=fun i=>(a i+k)*2)
      (family u a) (family u (fun i=>a i+k)) k (fun _=>rfl) r.val r.property⟩

def privateComputes : Computes (OrdinaryNegativeMixedBlockData.inputEncoding (u:=u) (a:=a))
    (OrdinaryNegativeMixedBlockData.inputEncoding (u:=u) (a:=fun i=>a i+k)) (privateQuery (u:=u) (a:=a) k) :=
  recode (W.queryComputes (s:=u) (a:=fun i=>a i*2) (b:=fun i=>(a i+k)*2)
    (family u a) (family u (fun i=>a i+k)) k (fun _=>rfl)) Subtype.val
    (fun _=>rfl) (fun _=>rfl)

def trace (i : Fin u) : Signature K (a i.val) :=
  fun z=>∑y : Fin k→Bool,coefficient H blocks i (Fin.addCases z y)

abbrev privateValue (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) : K :=
  C.value (s:=u) (arity:=fun i=>a i*2) (family u a) (trace H k blocks) r.val

omit [Algebra ℚ K] in
theorem private_query_value (r : OrdinaryNegativeMixedBlockData.Input (u:=u) (a:=a)) :
    value H blocks (privateQuery k r)=privateValue H k blocks r :=
  W.query_value (s:=u) (a:=fun i=>a i*2) (b:=fun i=>(a i+k)*2)
    (family u a) (family u (fun i=>a i+k)) k (fun _=>rfl) (coefficient H blocks) r.val r.property

def privateControlled : LengthControlledOracleReduction
    (OrdinaryNegativeMixedBlockData.inputEncoding (u:=u) (a:=a)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding (privateValue H k blocks)
    ((E.tables F H).evaluate F) :=
  Programme.compose
    (controlledOneQueryOfEq (privateComputes (u:=u) (a:=a) k)
      (identityComputes F.encoding)
      (controlled F H blocks e p₀ p₁ he h₀ h₁ balanced).sourceOutputBound
      (privateValue H k blocks) (fun r=>(private_query_value H k blocks r).symm))
    (controlled F H blocks e p₀ p₁ he h₀ h₁ balanced)

end Private
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockSource
end
