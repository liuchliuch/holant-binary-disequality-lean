import Holant.Proofs.Hardness.GeneralEOSupportHoleSourceProvenance
import Holant.Proofs.Hardness.GeneralEOCentralHoleSource

/-! Opposite original support-sign failures produce an actual original tensor
network and hence a counting source over the original dictionary plus directed01.
Only the label universe is enlarged: the input graph and its serialized rows
are unchanged. The descent chooses one fixed-family gadget; it does not assert
uniform polynomial synthesis of that gadget from a varying signature family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSupportHoleSource
open Computability Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace H
export GeneralEOCentralHoleSource (graph labels receipts source standardSource)
end H
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] GeneralEOCentralHoleSource.source
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (D : N.Source G)


abbrev graph := H.graph G D.graph (labels G D) (exact G D) (native G D) D.central D.hole
abbrev quaternaryLabels := H.labels G D.graph (labels G D) (exact G D) (native G D) D.central D.hole

theorem receipts :
    LabelledNetwork.Exact (P.palette G) (graph G D) (quaternaryLabels G D) ∧
    (∀ e,(graph G D).edge e=Signature.disequality) ∧
    Signature.CentralSupport (graph G D).denote ∧
    GeneralEONegativeSupportTensor.CentralHole (graph G D).denote :=
  H.receipts G D.graph (labels G D) (exact G D) (native G D) D.central D.hole

abbrev targetEncoding := GeneralEOCentralHoleHardness.targetEncoding (s:=s) (a:=a)
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

/-- The target uses the unchanged original generated field and answer codec. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (P.pinnedValue G) :=
  H.source G D.graph (labels G D) (exact G D) (native G D) D.central D.hole w

include D in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) := by
  intro α ea f w
  exact ⟨(source G D w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (P.pinnedValue G) :=
  source G D (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

variable (i j : Fin s) (hei : Signature.CentralSupport (G i))
variable (hej : Signature.CentralSupport (G j))
variable (hp : ¬EONegativeWitness.Supports .positive ⟨a i.val,G i⟩)
variable (hn : ¬EONegativeWitness.Supports .negative ⟨a j.val,G j⟩)

/-- No support tensor or quaternary gadget is supplied as an extra premise. -/
def fromFailures (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (P.pinnedValue G) :=
  source G (N.select G i j hei hej hp hn) w

def standardFromFailures : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (P.pinnedValue G) :=
  fromFailures G i j hei hej hp hn
    (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

include i j hei hej hp hn in
theorem failuresCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) := by
  intro α ea f w
  exact ⟨(fromFailures G i j hei hej hp hn w).reduction⟩

variable (p : EONegativePairReduction.Selection G)
variable (heo : ∀ g ∈ preprocess (EONegativePairReduction.family G),IsEO g)
variable (hs : ¬EONegativeWitness.Supports .positive (EONegativePairReduction.signature G p.first) ∧
  ¬EONegativeWitness.Supports .negative (EONegativePairReduction.signature G p.second))

/-- The support branch of an actual selected negative witness is consumed. -/
def fromSelection (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (P.pinnedValue G) :=
  source G (N.fromSelection G p heo hs) w

def standardFromSelection : LengthControlledOracleReduction ea encodingNatBool
    (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (P.pinnedValue G) :=
  fromSelection G p heo hs (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

include heo in
/-- The support branch now has an actual pinned counting source. The other
branch still records its original bad restrictions without asserting access. -/
theorem universal_dispatch
    (hbad : ¬EOTract (preprocess (EONegativePairReduction.family G))) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard
      (targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) ∨
    ∃ i j : Fin s,EONegativePairReduction.Kept G i ∧ EONegativePairReduction.Kept G j ∧
      ∃ p : OrientedPerfectPairing (a i.val),∃ q : OrientedPerfectPairing (a j.val),
        ¬Affine (p.restrict (G i)) ∧ ¬Product (q.restrict (G j)) := by
  rcases GeneralEONegativeSupportSource.universal_dispatch G heo hbad with hD | h
  · obtain ⟨D⟩ := hD
    exact Or.inl (witnessCountingHard G D)
  · exact Or.inr h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSupportHoleSource
