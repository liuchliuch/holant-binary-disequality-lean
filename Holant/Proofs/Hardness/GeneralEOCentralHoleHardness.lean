import Holant.Proofs.Hardness.GeneralEOPinnedDescentFieldBridge
import Holant.Proofs.Hardness.GeneralEONegativeSupportTensor
import Holant.Proofs.Hardness.EOQuaternaryOriginalSource

/-! An actual labelled quaternary central-hole network supplies counting
hardness over its original dictionary plus the literal directed 01 row.
The macro generated field and the original generated field are connected by
the implemented rational-linear retraction, never by an assumed codec equality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleHardness
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette (arity palette presentation pinnedValue)
end P
namespace B
export GeneralEOPinnedDescentFieldBridge (macroFamily macroPresentation macroValue source query_counts)
end B
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] EOQuaternaryOriginalSource.Family.source GeneralEOPinnedDescentFieldBridge.source

theorem not_tract {n : ℕ} {M : Signature AlgebraicComplex n}
    (hh : GeneralEONegativeSupportTensor.CentralHole M) : ¬EOTract {⟨n,M⟩} := by
  intro ht
  obtain ⟨_,_,sign,_,hs,_⟩ := ht
  exact GeneralEONegativeSupportTensor.centralHole_not_supports hh sign (hs _ (by simp))

theorem eoSupport (M : Signature AlgebraicComplex 4)
    (hc : Signature.CentralSupport M) : DenseEOUnitLocal.EOSupport M := by
  intro x hx
  apply hc
  omega

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (S : Network AlgebraicComplex 4)
variable (SL : Labelling S.shape (s+1) 1 (P.arity (s:=s) (a:=a)))
variable (he : LabelledNetwork.Exact (P.palette G) S SL)
variable (hn : ∀ e,S.edge e=Signature.disequality)
variable (hc : Signature.CentralSupport S.denote)
variable (hh : GeneralEONegativeSupportTensor.CentralHole S.denote)
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

abbrev targetEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (P.arity (s:=s) (a:=a))

/-- The actual quaternary source is first transported to the singleton macro
dictionary's generated field; this is a real selected-family programme. -/
def macroSource (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding 1 1 (fun _ => 4)) (B.macroPresentation S).encoding
    f (B.macroValue S) :=
  EOQuaternaryOriginalSource.Family.source (a:=fun _ => 4) S.denote (eoSupport S.denote hc) (not_tract hh)
    (B.macroFamily S) 0 rfl w

/-- Every reached oracle query is an original-family-plus-pin graph, encoded
in the unchanged original coefficient presentation. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (P.pinnedValue G) :=
  C.composeControlled (macroSource S hc hh w) (B.source G S SL he hn)

include S SL he hn hc hh in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) := by
  intro α ea f w
  exact ⟨(source G S SL he hn hc hh w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (P.pinnedValue G) :=
  source G S SL he hn hc hh (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleHardness
