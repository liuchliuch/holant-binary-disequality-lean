import Holant.Proofs.Hardness.GeneralEOAffinePlaneDEQSource
import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationProgramme
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Platonic.PhysicalCostComposition
import Holant.Proofs.CountingMachines.OracleControl.Storage

/-! The actual controlled same-field programme first amplifies arbitrary
literal pins, removes the one anchor in three queries, and physically expands
every resulting DEQ occurrence into the24-copy original-label chain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQProgramme
open Holant Holant.Complexity Holant.Algebraic Computability FixedGadgetSubstitution
namespace D
export GeneralEOAffinePlaneDEQSource
  (G g hg A coordinates tables signatures Input inputEncoding targetEncoding sourceValue new_signature native_tables)
end D
namespace P
export GeneralEOSinglePinAmplificationProgramme (source sourceValue inputEncoding)
end P
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K d) (T : ExactSignatureTables d s 1 a)
variable (j : Fin s) (M : Signature K 4)
variable (hM : (⟨a j.val,D.G F T j⟩ : AnySignature K)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4)) (c : K) (hc : c≠0)

def removeDEQ : LengthControlledOracleReduction
    (D.inputEncoding F T j M hM e) F.encoding
    (D.targetEncoding (s:=s) (a:=a)) F.encoding
    (D.sourceValue F T j M hM e c) (T.evaluate F) :=
  Holant.LocalDrafts.Hardness.ControlledCap.scaledAdjoin F T
    (D.g F T j M hM e) (D.hg F T j M hM e) c hc

abbrev templates := Adjoin.templates s a (D.g F T j M hM e)
abbrev templateValid := Adjoin.wellFormed (D.g F T j M hM e) (D.hg F T j M hM e)
abbrev query := Compiler.value (s+1) 1 (D.A F T j M hM e)
  (templates F T j M hM e) s a
    (compilerHypotheses (templates F T j M hM e) (templateValid F T j M hM e))

/- The context is exactly the actual number of E-labelled source vertices. -/
include hc in
theorem local_denote (i : Fin (s+1)) :
    ((templates F T j M hM e i.val).network (templateValid F T j M hM e i.val i.isLt)
      (D.G F T) (fun i b b' => F.decode (T.edge i b b'))).denote=
        (if i.val=s then c else 1) • (D.signatures F T j M hM e c i) := by
  funext x
  change _=(if i.val=s then c else 1)*F.decode
    (ScaledAdjoin.coordinates F T (D.g F T j M hM e) (D.hg F T j M hM e) c i x)
  unfold ScaledAdjoin.coordinates ScaledAdjoin.rescale
  rw [LinearEquiv.apply_symm_apply]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates]
  have hn : (if i.val=s then c else 1)≠0 := by split_ifs <;> simp_all
  field_simp
  rfl

include hc in
theorem query_value (r : D.Input F T j M hM e) :
    T.evaluate F (query F T j M hM e r)=
      c^occurrences s r.val*D.sourceValue F T j M hM e c r := by
  exact replacement_scale_power (templates F T j M hM e) r.val r.property
    (templateValid F T j M hM e) (D.signatures F T j M hM e c) (D.G F T)
    (fun i b b' => F.decode (T.edge i b b')) s c (local_denote F T j M hM e c hc)

include hc in
theorem corrected_value (r : D.Input F T j M hM e) :
    T.evaluate F (query F T j M hM e r)/(c^occurrences s r.val)=
      D.sourceValue F T j M hM e c r := by
  rw [query_value F T j M hM e c hc r]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)

variable (hn : ∀i b b',F.decode (T.edge i b b')=Signature.disequality b b')
variable (f : Signature K 2) (hplane : Tensor.reindex e M=EOBinaryPlaneCore.lift f)
variable (hp : GeneralEOAffinePlaneChain.table f^24=c • (1 : GeneralEOAffinePlaneChain.Mat (K:=K)))

abbrev amplifier := P.source F (D.tables F T j M hM e c)
  (D.native_tables F T j M hM e c hn) ⟨s,Nat.lt_succ_self s⟩
    (D.new_signature F T j M hM e c hn f hplane hp hc)

/-- No E row remains in the target oracle. Every subprogramme uses exactly
F.encoding, and controlled inlining supplies query, answer, time and storage
bounds for the same finite machine. -/
def sourceWithDEQ : LengthControlledOracleReduction
    (P.inputEncoding (s:=s+1) (a:=D.A F T j M hM e)) F.encoding
    (D.targetEncoding (s:=s) (a:=a)) F.encoding
    (P.sourceValue F (D.tables F T j M hM e c)) (T.evaluate F) :=
  C.composeControlled (amplifier F T j M hM e c hc hn f hplane hp)
    (removeDEQ F T j M hM e c hc)

theorem query_origin (oracle : List Bool→List Bool)
    (ho : RepresentsOracle (D.targetEncoding (s:=s) (a:=a)) F.encoding (T.evaluate F) oracle)
    (r : GeneralEOSinglePinAmplificationCompiler.Input (s:=s+1) (a:=D.A F T j M hM e))
    (t : ℕ) (z : (sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.Cfg)
    (hr : (sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.run oracle
      ((P.inputEncoding (s:=s+1) (a:=D.A F T j M hM e)).encode r) t=some z)
    (hq : (sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.IsQuery z) :
    ∃q : ExactSignatureTables.Input s 1 a,
      z.stk (sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.queryStack=
        (D.targetEncoding (s:=s) (a:=a)).encode q ∧
      (z.stk (sourceWithDEQ F T j M hM e c hc hn f hplane hp).reduction.machine.queryStack).length≤
        (sourceWithDEQ F T j M hM e c hc hn f hplane hp).queryBound.eval
          ((P.inputEncoding (s:=s+1) (a:=D.A F T j M hM e)).encode r).length :=
  (sourceWithDEQ F T j M hM e c hc hn f hplane hp).safeQuery oracle ho r t z hr hq

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneDEQProgramme
