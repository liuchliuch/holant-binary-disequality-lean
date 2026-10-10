import Holant.Proofs.Hardness.GeneralEOSinglePinProgramme
import Holant.Proofs.Hardness.GeneralEONonARSPinningFieldBridge

/-! MWX Lemma 34 in the unchanged original coefficient field and codec.
The only source promise is at most one literal 01 vertex. Internal physical
graph selection and the native-edge smoothing compiler supply all queries.
This result is stronger than the EO specialization: no support hypothesis is
needed by the three-query reconstruction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinSource
open Computability Holant Holant.Algebraic Holant.Complexity Holant.Tractable
open UniversalPairReduction FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue target_exact)
end O
namespace P
export GeneralEOSinglePinProgramme (Mode mode value pre query reduction controlled run_trace exact_calls)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
abbrev original := GeneralEOBinaryPinSource.original G
abbrev presentation := O.originalPresentation G
abbrev Input := UniversalPairReduction.Input s a
abbrev inputEncoding := UniversalPairReduction.inputEncoding s a
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev sourceValue := P.value (presentation G) (O.originalTables G)

theorem source_promise (r : Input (s:=s) (a:=a)) : occurrences s r.val≤1 := r.property.2

theorem input_literal (r : Input (s:=s) (a:=a)) :
    (inputEncoding (s:=s) (a:=a)).encode r=RawClosedNetwork.encoding.encode r.val := rfl

theorem decoded_original : ValueJoins.signatures (presentation G) (O.originalTables G)=original G := by
  funext i x
  exact LinearEquiv.apply_symm_apply _ _

theorem native_tables : ∀i b c,(presentation G).decode ((O.originalTables G).edge i b c)=
    Signature.disequality b c := by
  intro i b c
  exact LinearEquiv.apply_symm_apply _ _

theorem programme_value : sourceValue G=BinaryFamily.value (original G) BinaryTable.delta := by
  change BinaryFamily.value (ValueJoins.signatures (presentation G) (O.originalTables G)) BinaryTable.delta=_
  rw [decoded_original]

/-- Exact ambient meaning, with every original arity and value retained. The
new row is literally one on 01 and zero on the other three bit strings. -/
theorem source_value_exact (r : Input (s:=s) (a:=a)) :
    ((sourceValue G r : O.originalField G) : AlgebraicComplex)=
      (r.val.realize r.property.1 (BinaryFamily.signatures G BinaryTable.delta)
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  rw [programme_value]
  unfold BinaryFamily.value
  change (O.originalField G).subtype _=_
  rw [←Network.denote_map (O.originalField G).subtype]
  congr 1
  unfold BinaryFamily.network Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    dsimp only
    unfold BinaryFamily.signatures
    split_ifs with hi
    · rfl
    · change ((BinaryTable.delta _ _ : O.originalField G) : AlgebraicComplex)=BinaryTable.delta _ _
      simp only [BinaryTable.delta]
      split_ifs <;> rfl
  · funext e b c
    cases b <;> cases c <;> rfl

abbrev selected := P.mode (presentation G) (O.originalTables G)
abbrev query (i : Fin 3) := P.query (presentation G) (O.originalTables G) (selected G) i
abbrev queries (r : Input (s:=s) (a:=a)) :=
  (P.pre (presentation G) (O.originalTables G) (selected G) r).1

/-- A real polynomial-time oracle machine, with bounded and validated queries,
over precisely originalValue G. There is no extra target vertex or coefficient. -/
def source : LengthControlledOracleReduction (inputEncoding (s:=s) (a:=a)) (presentation G).encoding
    (targetEncoding (s:=s) (a:=a)) (presentation G).encoding
    (sourceValue G) (O.originalValue G) :=
  P.controlled (presentation G) (O.originalTables G) (selected G) (native_tables G)

theorem exact_transcript (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) (presentation G).encoding
      (O.originalValue G) oracle) (r : Input (s:=s) (a:=a)) :
    ∃n≤(source G).reduction.time.eval ((inputEncoding (s:=s) (a:=a)).encode r).length,
      OracleBatch.RunsTrace (source G).reduction.machine oracle
        ((source G).reduction.machine.init ((inputEncoding (s:=s) (a:=a)).encode r))
        ((source G).reduction.machine.output ((presentation G).encoding.encode (sourceValue G r))) n
        ((queries G r).map (targetEncoding (s:=s) (a:=a)).encode) :=
  P.run_trace (presentation G) (O.originalTables G) (selected G) (native_tables G) oracle ho r

theorem exact_three_calls (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) (presentation G).encoding
      (O.originalValue G) oracle) (r : Input (s:=s) (a:=a)) :
    ∃n≤(source G).reduction.time.eval ((inputEncoding (s:=s) (a:=a)).encode r).length,
      ThreeQuery.queryCount (source G).reduction.machine oracle
        ((source G).reduction.machine.init ((inputEncoding (s:=s) (a:=a)).encode r)) n=3 := by
  obtain ⟨n,hn,ht⟩ := exact_transcript G oracle ho r
  exact ⟨n,hn,by simpa only [queries,GeneralEOSinglePinProgramme.pre,List.length_map,
    List.length_cons,List.length_nil] using ht.count⟩

/-- The first physical query is always the original native-edge splice;
its circle case contributes the existing exact factor two inside the decoder. -/
theorem first_query (r : Input (s:=s) (a:=a)) : query G 0 r=Surgery.query r := by
  unfold query GeneralEOSinglePinProgramme.query
  cases selected G <;> rfl

theorem first_query_size (r : Input (s:=s) (a:=a)) :
    (query G 0 r).val.vertices.length+(query G 0 r).val.edges.length≤
      r.val.vertices.length+r.val.edges.length := by
  rw [first_query]
  exact Smoothing.compile_counts_le s r.val

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinSource
