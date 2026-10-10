import Holant.Proofs.Hardness.GeneralEOCentralHoleInduction
import Holant.Proofs.Hardness.GeneralEOCentralHoleHardness

/-! Arbitrary-arity central-hole counting source. The quaternary graph is
obtained by proved finite physical descent, then compiled into the actual
original dictionary plus directed01. Selection is fixed-family gadget
selection; no uniform polynomial gadget-synthesis claim is made. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleSource
open Computability Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette
  (arity palette pinLabel palette_pin corollaLabels corolla_exact presentation pinnedValue)
end P
namespace I
export GeneralEOCentralHoleInduction (QuaternaryHole reduce)
end I
namespace H
export GeneralEONegativeSupportTensor (CentralHole)
end H
namespace Q
export GeneralEOCentralHoleHardness (targetEncoding source)
end Q
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] GeneralEOCentralHoleHardness.source
variable {s n : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (S : Network AlgebraicComplex n)
variable (SL : Labelling S.shape (s+1) 1 (P.arity (s:=s) (a:=a)))
variable (hL : LabelledNetwork.Exact (P.palette G) S SL)
variable (hn : ∀i,S.edge i=Signature.disequality)
variable (he : Signature.CentralSupport S.denote) (hh : H.CentralHole S.denote)

include S SL hL hn he hh in
theorem endpoint_exists : I.QuaternaryHole (P.palette G) :=
  I.reduce (P.palette G) P.pinLabel (P.palette_pin G) n S SL hL hn he hh

def graph : Network AlgebraicComplex 4 :=
  Classical.choose (endpoint_exists G S SL hL hn he hh)

def labels : Labelling (graph G S SL hL hn he hh).shape (s+1) 1 (P.arity (s:=s) (a:=a)) :=
  Classical.choose (Classical.choose_spec (endpoint_exists G S SL hL hn he hh))

theorem receipts :
    LabelledNetwork.Exact (P.palette G) (graph G S SL hL hn he hh) (labels G S SL hL hn he hh) ∧
    (∀i,(graph G S SL hL hn he hh).edge i=Signature.disequality) ∧
    Signature.CentralSupport (graph G S SL hL hn he hh).denote ∧
    H.CentralHole (graph G S SL hL hn he hh).denote :=
  Classical.choose_spec (Classical.choose_spec (endpoint_exists G S SL hL hn he hh))

variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (Q.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (P.pinnedValue G) :=
  Q.source G (graph G S SL hL hn he hh) (labels G S SL hL hn he hh)
    (receipts G S SL hL hn he hh).1 (receipts G S SL hL hn he hh).2.1
    (receipts G S SL hL hn he hh).2.2.1 (receipts G S SL hL hn he hh).2.2.2 w

include S SL hL hn he hh in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (Q.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding (P.pinnedValue G) := by
  intro α ea f w
  exact ⟨(source G S SL hL hn he hh w).reduction⟩

variable {Δ Qstate : Type} [Fintype Δ] [Fintype Qstate]
variable (m : Standard.Model Δ Qstate) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (Q.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (P.pinnedValue G) :=
  source G S SL hL hn he hh (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

/-- One actual original row can start the induction at any arity. -/
def sourceOfRow (i : Fin s) (hc : Signature.CentralSupport (G i))
    (h : H.CentralHole (G i)) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool
      (Q.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (P.pinnedValue G) :=
  source G (Network.corolla (G i)) (P.corollaLabels G i) (P.corolla_exact G i)
    (fun e => Fin.elim0 e) (by simpa only [Network.denote_corolla] using hc)
    (by simpa only [Network.denote_corolla] using h) w

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleSource
