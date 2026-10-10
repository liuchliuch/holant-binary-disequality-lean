import Holant.Proofs.Hardness.GeneralEOAffineNetworkDEQSource
import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationProgramme
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Platonic.PhysicalCostComposition
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! The actual controlled same-field programme first amplifies arbitrary
literal pins, removes the one anchor in three queries, and physically expands
every resulting DEQ occurrence into the 24-copy actual-network chain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkDEQProgramme
open Holant Holant.Complexity Holant.Algebraic Computability FixedGadgetSubstitution
namespace D
export GeneralEOAffineNetworkDEQSource
  (G g hg A coordinates tables signatures Input inputEncoding targetEncoding sourceValue new_signature native_tables)
end D
namespace P
export GeneralEOSinglePinAmplificationProgramme (source sourceValue inputEncoding)
end P
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (N : Network K 4) (NL : Labelling N.shape s 1 a)
variable (e : Equiv.Perm (Fin 4)) (c : K) (hc : c≠0)

def removeDEQ : LengthControlledOracleReduction
    (D.inputEncoding N NL e) F.encoding
    (D.targetEncoding (s:=s) (a:=a)) F.encoding
    (D.sourceValue F T N NL e c) (T.evaluate F) :=
  Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin F T
    (D.g N NL e) (D.hg N NL e) c hc

abbrev templates := Adjoin.templates s a (D.g N NL e)
abbrev templateValid := Adjoin.wellFormed (D.g N NL e) (D.hg N NL e)
abbrev query := Compiler.value (s+1) 1 (D.A N NL e)
  (templates N NL e) s a
    (compilerHypotheses (templates N NL e) (templateValid N NL e))

/- The context is exactly the actual number of E-labelled source vertices. -/
include hc in
theorem local_denote (i : Fin (s+1)) :
    ((templates N NL e i.val).network (templateValid N NL e i.val i.isLt)
      (D.G F T) (fun i b b' => F.decode (T.edge i b b'))).denote=
        (if i.val=s then c else 1) • (D.signatures F T N NL e c i) := by
  funext x
  change _=(if i.val=s then c else 1)*F.decode
    (ScaledAdjoin.coordinates F T (D.g N NL e) (D.hg N NL e) c i x)
  unfold ScaledAdjoin.coordinates ScaledAdjoin.rescale
  rw [LinearEquiv.apply_symm_apply]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates]
  have hn : (if i.val=s then c else 1)≠0 := by split_ifs <;> simp_all
  field_simp
  rfl

include hc in
theorem query_value (r : D.Input N NL e) :
    T.evaluate F (query N NL e r)=
      c^occurrences s r.val*D.sourceValue F T N NL e c r := by
  exact replacement_scale_power (templates N NL e) r.val r.property
    (templateValid N NL e) (D.signatures F T N NL e c) (D.G F T)
    (fun i b b' => F.decode (T.edge i b b')) s c (local_denote F T N NL e c hc)

include hc in
theorem corrected_value (r : D.Input N NL e) :
    T.evaluate F (query N NL e r)/(c^occurrences s r.val)=
      D.sourceValue F T N NL e c r := by
  rw [query_value F T N NL e c hc r]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)

variable (hn : ∀i b b',F.decode (T.edge i b b')=Signature.disequality b b')
variable (hN : LabelledNetwork.Exact (D.G F T) N NL)
variable (hNative : ∀i,N.edge i=Signature.disequality)
variable (f : Signature K 2) (hplane : Tensor.reindex e N.denote=EOBinaryPlaneCore.lift f)
variable (hp : GeneralEOAffinePlaneChain.table f^24=c • (1 : GeneralEOAffinePlaneChain.Mat (K:=K)))

abbrev amplifier := P.source F (D.tables F T N NL e c)
  (D.native_tables F T N NL e c hn) ⟨s,Nat.lt_succ_self s⟩
    (D.new_signature F T N NL e c hn hN hNative f hplane hp hc)

/-- No E row remains in the target oracle. Every subprogramme uses exactly
F.encoding, and controlled inlining supplies query, answer, time and storage
bounds for the same finite machine. -/
def sourceWithDEQ : LengthControlledOracleReduction
    (P.inputEncoding (s:=s+1) (a:=D.A N NL e)) F.encoding
    (D.targetEncoding (s:=s) (a:=a)) F.encoding
    (P.sourceValue F (D.tables F T N NL e c)) (T.evaluate F) :=
  C.composeControlled (amplifier F T N NL e c hc hn hN hNative f hplane hp)
    (removeDEQ F T N NL e c hc)

attribute [local irreducible] sourceWithDEQ

theorem query_origin (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (D.targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : GeneralEOSinglePinAmplificationCompiler.Input (s:=s+1) (a:=D.A N NL e))
    (t : ℕ) (z : (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.Cfg)
    (hr : (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.run oracle
      ((P.inputEncoding (s:=s+1) (a:=D.A N NL e)).encode r) t=some z)
    (hq : (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.IsQuery z) :
    ∃q : ExactSignatureTables.Input s 1 a,
      z.stk (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.queryStack=
        (D.targetEncoding (s:=s) (a:=a)).encode q ∧
      (z.stk (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).reduction.machine.queryStack).length≤
        (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).queryBound.eval
          ((P.inputEncoding (s:=s+1) (a:=D.A N NL e)).encode r).length :=
  (sourceWithDEQ F T N NL e c hc hn hN hNative f hplane hp).safeQuery oracle ho r t z hr hq

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkDEQProgramme
