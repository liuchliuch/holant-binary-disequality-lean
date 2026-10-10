import Holant.Proofs.Hardness.SelectedOriginalFamily

/-! Actual finite original-label selection for arbitrary arities. The query
rewrites labels only. Coefficient-generated source and target fields stay
distinct, and the returned answer runs through a fixed rational retraction.
This is a physical reduction, not a promised family-hardness endpoint. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeSubfamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients originalField originalPresentation originalTables originalValue target_exact)
end O
namespace Choice
export UniversalPairReduction.Surgery.Choice (table evaluate denote_eq_evaluate)
end Choice
namespace Cost
export Holant.LocalDrafts.RemoteWork.CountingBridge.OracleControl
  (runFee feePolynomial runFee_le configurationWord codedStoragePolynomial coded_storage_le)
end Cost
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

variable {s m : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (σ : ℕ → ℕ) (hb : ∀ i : Fin m, σ i.val < s)

def label (i : Fin m) : Fin s := ⟨σ i.val, hb i⟩
def selectedArity (k : ℕ) : ℕ := a (σ k)
def selected : (i : Fin m) → Signature AlgebraicComplex (selectedArity (a:=a) σ i.val) :=
  fun i => G (label σ hb i)

abbrev sourceEncoding := RawClosedNetwork.validatedEncoding m 1 (selectedArity (a:=a) σ)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev Input := ExactSignatureTables.Input m 1 (selectedArity (a:=a) σ)
abbrev TargetInput := ExactSignatureTables.Input s 1 a

local instance sourceAlgebra : Algebra ℚ (O.originalField (selected G σ hb)) :=
  (O.originalField (selected G σ hb)).algebra'
local instance targetAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

def query : Input (m:=m) (a:=a) σ → TargetInput (s:=s) (a:=a) :=
  Relabel.input (label σ hb) (fun _ => rfl)

def queryComputes : Computes (sourceEncoding (m:=m) (a:=a) σ) (targetEncoding (s:=s) (a:=a))
    (query (a:=a) σ hb) := Relabel.computes (label σ hb) (fun _ => rfl)

/-- Every requested original label is retained, even if two labels name
identical tensors or the selected index list repeats a label. -/
theorem query_rows (r : Input (m:=m) (a:=a) σ) :
    (query σ hb r).val.vertices = r.val.vertices.map (fun v => (σ v.1, v.2)) := by
  change r.val.vertices.map (Relabel.row (label σ hb)) = _
  apply List.map_congr_left
  intro v hv
  have hi := (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 v hv).1
  simp [Relabel.row, Relabel.label, hi, label]

theorem query_ports (r : Input (m:=m) (a:=a) σ) :
    (query σ hb r).val.vertices.map Prod.snd = r.val.vertices.map Prod.snd :=
  Relabel.ordered_ports (label σ hb) r.val

theorem query_edges (r : Input (m:=m) (a:=a) σ) : (query σ hb r).val.edges = r.val.edges := rfl

theorem query_vertices_length (r : Input (m:=m) (a:=a) σ) :
    (query σ hb r).val.vertices.length = r.val.vertices.length :=
  Relabel.vertices_length (label σ hb) r.val

/-- The selected field is included because each generator is an original
coefficient. No macro, interpolation constant, or basis is adjoined. -/
theorem field_le : O.originalField (selected G σ hb) ≤ O.originalField G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i, rfl⟩
  exact coefficient_mem_familyField (O.coefficients G) ⟨label σ hb i.1, i.2⟩

def embedding : O.originalField (selected G σ hb) →ₐ[ℚ] O.originalField G :=
  IntermediateField.inclusion (field_le G σ hb)

theorem embedding_value (x : O.originalField (selected G σ hb)) :
    (embedding G σ hb x : AlgebraicComplex) = x :=
  IntermediateField.coe_inclusion (field_le G σ hb) x

theorem table_label (i : Fin m) (bits : List Bool) :
    Choice.table (selected G σ hb) i.val bits = Choice.table G (label σ hb i).val bits := by
  simp only [Choice.table, dif_pos i.isLt, dif_pos (label σ hb i).isLt]
  rfl

theorem ambient_query (r : Input (m:=m) (a:=a) σ) :
    ((query σ hb r).val.realize (query σ hb r).property G
      (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 =
    (r.val.realize r.property (selected G σ hb)
      (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
  have h := Relabel.value_scaled (c:=a) (label σ hb) (Choice.table (selected G σ hb))
    (Choice.table G) (fun _ => (1 : AlgebraicComplex)) (fun _ => rfl) r
    (fun i bits => by simpa using table_label G σ hb i bits)
  have hp : Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin m => (1 : AlgebraicComplex)) r.val = 1 := by
    unfold Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
    apply List.prod_eq_one
    intro z hz
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hrow
    simp only [Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.total,
      dif_pos (r.property.1 i).1]
  rw [hp, one_mul] at h
  rw [Choice.denote_eq_evaluate, Choice.denote_eq_evaluate]
  exact h.symm

theorem query_value (r : Input (m:=m) (a:=a) σ) :
    O.originalValue G (query σ hb r) =
      embedding G σ hb (O.originalValue (selected G σ hb) r) := by
  apply Subtype.ext
  rw [O.target_exact, embedding_value, O.target_exact]
  exact ambient_query G σ hb r

def answer := (embedding G σ hb).toLinearMap.leftInverse

def answerComputes : Computes (O.originalPresentation G).encoding
    (O.originalPresentation (selected G σ hb)).encoding (answer G σ hb) :=
  FieldCodec.retractComputes (O.originalPresentation (selected G σ hb))
    (O.originalPresentation G) (embedding G σ hb)

def controlled : LengthControlledOracleReduction (sourceEncoding (m:=m) (a:=a) σ)
    (O.originalPresentation (selected G σ hb)).encoding
    (targetEncoding (s:=s) (a:=a)) (O.originalPresentation G).encoding
    (O.originalValue (selected G σ hb)) (O.originalValue G) :=
  controlledOneQueryOfEq (queryComputes σ hb) (answerComputes G σ hb)
    ((O.originalTables G).outputBound (O.originalPresentation G))
    (O.originalValue (selected G σ hb)) (fun r => by
      change O.originalValue (selected G σ hb) r = answer G σ hb (O.originalValue G (query σ hb r))
      rw [query_value]
      exact (FieldCodec.retract_embedding (embedding G σ hb) _).symm)

theorem answer_recovers (r : Input (m:=m) (a:=a) σ) :
    answer G σ hb (O.originalValue G (query σ hb r)) = O.originalValue (selected G σ hb) r := by
  rw [query_value]
  exact FieldCodec.retract_embedding (embedding G σ hb) _

theorem recovered_bytes (r : Input (m:=m) (a:=a) σ) :
    (O.originalPresentation (selected G σ hb)).encoding.encode
      (answer G σ hb (O.originalValue G (query σ hb r))) =
    (O.originalPresentation (selected G σ hb)).encoding.encode (O.originalValue (selected G σ hb) r) :=
  congrArg (O.originalPresentation (selected G σ hb)).encoding.encode (answer_recovers G σ hb r)

def outputs (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle) (r : Input (m:=m) (a:=a) σ) :=
  (controlled G σ hb).reduction.correct oracle ho r

theorem prefix_fees (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle) (r : Input (m:=m) (a:=a) σ) (t : ℕ)
    (ht : t ≤ (controlled G σ hb).reduction.time.eval ((sourceEncoding (m:=m) (a:=a) σ).encode r).length) :
    Cost.runFee (controlled G σ hb).reduction.machine oracle ((sourceEncoding (m:=m) (a:=a) σ).encode r) t ≤
      (Cost.feePolynomial (controlled G σ hb)).eval ((sourceEncoding (m:=m) (a:=a) σ).encode r).length :=
  Cost.runFee_le (controlled G σ hb) oracle ho r t ht

theorem prefix_storage (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (targetEncoding (s:=s) (a:=a)) (O.originalPresentation G).encoding
      (O.originalValue G) oracle) (r : Input (m:=m) (a:=a) σ) (t : ℕ)
    (ht : t ≤ (controlled G σ hb).reduction.time.eval ((sourceEncoding (m:=m) (a:=a) σ).encode r).length)
    (c : (controlled G σ hb).reduction.machine.Cfg)
    (hr : (controlled G σ hb).reduction.machine.run oracle ((sourceEncoding (m:=m) (a:=a) σ).encode r) t = some c) :
    (Cost.configurationWord (controlled G σ hb).reduction.machine c).length ≤
      (Cost.codedStoragePolynomial (controlled G σ hb)).eval ((sourceEncoding (m:=m) (a:=a) σ).encode r).length :=
  Cost.coded_storage_le (controlled G σ hb) oracle ho r t ht c hr

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeSubfamily
