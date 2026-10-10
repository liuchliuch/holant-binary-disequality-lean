import Holant.Proofs.Hardness.GeneralEOAffineNetworkDEQProgramme
import Holant.Proofs.Hardness.GeneralEOSinglePinDEQInclusion

/-! Arbitrarily many literal directed01 pins reduce to the unchanged original
finite family. A physical label-inclusion prefix supplies no E vertices; all
DEQ occurrences introduced by the anchor programme are expanded to original
vertices, and each scalar is corrected in the same original coefficient codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkPinSource
open Holant Holant.Complexity Holant.Algebraic Computability FixedGadgetSubstitution
namespace D
export GeneralEOAffineNetworkDEQSource (G A tables signatures old_signature targetEncoding)
end D
namespace P
export GeneralEOSinglePinAmplificationProgramme (Input inputEncoding sourceValue)
end P
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace R
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (configurationWord codedStoragePolynomial coded_storage_le)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (N : Network K 4) (NL : Labelling N.shape s 1 a)
variable (e : Equiv.Perm (Fin 4)) (c : K) (hc : c≠0)
variable (hn : ∀i b b',F.decode (T.edge i b b')=Signature.disequality b b')
variable (hN : LabelledNetwork.Exact (D.G F T) N NL)
variable (hNative : ∀i,N.edge i=Signature.disequality)
variable (f : Signature K 2) (hplane : Tensor.reindex e N.denote=EOBinaryPlaneCore.lift f)
variable (hp : GeneralEOAffinePlaneChain.table f^24=c • (1 : GeneralEOAffinePlaneChain.Mat (K:=K)))

/-- Full literal original-G-plus01 input, original-G-only queries and the
unchanged field presentation F on both ends of the actual compiled machine. -/
def source : LengthControlledOracleReduction
    (P.inputEncoding (s:=s) (a:=a)) F.encoding
    (D.targetEncoding (s:=s) (a:=a)) F.encoding (P.sourceValue F T) (T.evaluate F) :=
  C.composeControlled
    (GeneralEOSinglePinDEQInclusion.source F T (D.signatures F T N NL e c)
      (D.old_signature F T N NL e c))
    (GeneralEOAffineNetworkDEQProgramme.sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp)

attribute [local irreducible] source

/-- Every runtime oracle word parses as an original-family native-X graph. -/
theorem query_origin (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (D.targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : P.Input (s:=s) (a:=a)) (t : ℕ)
    (z : (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.Cfg)
    (hr : (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.run oracle
      ((P.inputEncoding (s:=s) (a:=a)).encode r) t=some z)
    (hq : (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.IsQuery z) :
    ∃q : ExactSignatureTables.Input s 1 a,
      z.stk (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.queryStack=
        (D.targetEncoding (s:=s) (a:=a)).encode q ∧
      (z.stk (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.queryStack).length≤
        (source F T N NL e c hc hn hN hNative f hplane hp).queryBound.eval
          ((P.inputEncoding (s:=s) (a:=a)).encode r).length :=
  (source F T N NL e c hc hn hN hNative f hplane hp).safeQuery oracle ho r t z hr hq

/-- Polynomial storage refers to the faithful encoding of the actual compiled
configuration, including control and all live and stale stack contents. -/
theorem coded_storage (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (D.targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : P.Input (s:=s) (a:=a)) (t : ℕ)
    (ht : t≤(source F T N NL e c hc hn hN hNative f hplane hp).reduction.time.eval
      ((P.inputEncoding (s:=s) (a:=a)).encode r).length)
    (z : (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.Cfg)
    (hr : (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.run oracle
      ((P.inputEncoding (s:=s) (a:=a)).encode r) t=some z) :
    (R.configurationWord (source F T N NL e c hc hn hN hNative f hplane hp).reduction.machine z).length≤
      (R.codedStoragePolynomial (source F T N NL e c hc hn hN hNative f hplane hp)).eval
        ((P.inputEncoding (s:=s) (a:=a)).encode r).length :=
  R.coded_storage_le (source F T N NL e c hc hn hN hNative f hplane hp) oracle ho r t ht z hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkPinSource
