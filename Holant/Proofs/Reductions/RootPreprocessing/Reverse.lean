import Holant.Proofs.Reductions.RootPreprocessing.Reduction


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable Holant.Complexity.GraphPreprocessing
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open UniversalPairReduction.Surgery
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open FactorSaturation
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def originalLabel (i : ℕ) : ℕ := if hi : i < count G then (includeLabel G ⟨i,hi⟩).val else 0
@[simp] theorem originalLabel_fin (j : Fin (count G)) :
    originalLabel G j.val = (includeLabel G j).val := by simp only [originalLabel,dif_pos j.isLt]
def includeRow (row : RawVertex) : RawVertex := (originalLabel G row.1,row.2)
def includedRaw (r : RawClosedNetwork) : RawClosedNetwork := ⟨r.vertices.map (includeRow G),r.edges⟩

theorem included_wellFormed (r : TargetInput G) : (includedRaw G r.val).WellFormed s 1 a := by
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_,hr.2.1,?_⟩
  · intro q hq
    obtain ⟨row,hm,rfl⟩ := List.mem_map.mp hq
    have hrow := hr.1 row hm
    let j : Fin (count G) := ⟨row.1,hrow.1⟩
    change originalLabel G j.val < s ∧ row.2.length = a (originalLabel G j.val)
    rw [originalLabel_fin]
    exact ⟨(includeLabel G j).isLt,hrow.2.trans (target_arity G j)⟩
  · simpa [includedRaw,endpoints,expectedEndpoints,includeRow,List.map_map,Function.comp_def] using hr.2.2

def includeInput (r : TargetInput G) : Input (s:=s) (a:=a) :=
  ⟨includedRaw G r.val,included_wellFormed G r⟩

def includeComputes : Computes (validatedEncoding (count G) 1 (targetArity G))
    (sourceEncoding (s:=s) (a:=a)) (includeInput G) := by
  let row : Computes (queryEncoding (count G) 1 (targetArity G)) vertexEncoding
      (fun x => ((includeLabel G (sourceLabel (count G) 1 (targetArity G) x)).val,
        (x.1.val.vertices.get x.2).2)) := recode (pairComputes
    (labelRecodeComputes (count G) 1 (targetArity G) encodingNatBool
      (fun j => (includeLabel G j).val))
    (GroupingMachine.rowPortsComputes (count G) 1 (targetArity G))) id
      (fun _ => rfl) (fun _ => rfl)
  let provider : Computes (queryEncoding (count G) 1 (targetArity G)) Frame.wordEncoding
      (fun x => entries vertexEncoding [includeRow G (x.1.val.vertices.get x.2)]) :=
    congrComputes (row.andThen (entryComputes vertexEncoding))
    (fun x => by
      let j := sourceLabel (count G) 1 (targetArity G) x
      have hj : originalLabel G (x.1.val.vertices.get x.2).1 = (includeLabel G j).val :=
        originalLabel_fin G j
      change entry vertexEncoding ((includeLabel G j).val,(x.1.val.vertices.get x.2).2) = _
      simp only [includeRow,hj,entries,List.flatMap_cons,List.flatMap_nil,List.append_nil])
  let rows := RowProgram.computes (fun row => [includeRow G row]) provider
  refine recode (pairComputes rows (edgesComputes (count G) 1 (targetArity G)))
    id (fun _ => rfl) ?_
  intro r
  simp only [← List.map_eq_flatMap] <;> rfl

theorem include_ambient (r : TargetInput G) :
    ambientValue G (includeInput G r) = targetAmbient G r := by
  unfold ambientValue targetAmbient Holant.LocalDrafts.Hardness.RootPreprocessing.nativeX
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  unfold Choice.weight
  change ((r.val.vertices.map (includeRow G)).map _).prod = _
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row hm
  have hi := (((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 row hm).1
  let j : Fin (count G) := ⟨row.1,hi⟩
  change Choice.table G (originalLabel G j.val) (row.2.map (Choice.bit (Choice.extend c))) =
    Choice.table (targetTable G) j.val (row.2.map (Choice.bit (Choice.extend c)))
  rw [originalLabel_fin,target_table]
  simp [Choice.table,(includeLabel G j).isLt]

theorem include_value (r : TargetInput G) : sourceValue G (includeInput G r) =
    embedding G (retainedValue G r) := by
  apply Subtype.ext
  change (sourceValue G (includeInput G r) : AlgebraicComplex) = (retainedValue G r : AlgebraicComplex)
  rw [source_exact,retained_exact_value]
  exact include_ambient G r

variable (hI : RetainsIdentity (Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))))

def reverse : LengthControlledOracleReduction
    (OriginalCodec.encoding (roots G hI)) (OriginalCodec.presentation (roots G hI)).encoding
    (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (OriginalCodec.value (roots G hI)) (sourceValue G) :=
  controlledOneQueryOfEq (includeComputes G) (retractComputes G)
    ((sourceTables G).outputBound (sourcePresentation G)) (retainedValue G)
    (fun r => by
      change retainedValue G r = (embedding G).toLinearMap.leftInverse (sourceValue G (includeInput G r))
      rw [include_value]
      exact (FieldCodec.retract_embedding (embedding G) (retainedValue G r)).symm)

theorem equivalent :
    OracleReducible (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
      (OriginalCodec.encoding (roots G hI)) (OriginalCodec.presentation (roots G hI)).encoding
      (sourceValue G) (OriginalCodec.value (roots G hI)) ∧
    OracleReducible (OriginalCodec.encoding (roots G hI)) (OriginalCodec.presentation (roots G hI)).encoding
      (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
      (OriginalCodec.value (roots G hI)) (sourceValue G) :=
  ⟨⟨reduction G hI⟩,⟨(reverse G hI).reduction⟩⟩

end Holant.LocalDrafts.Hardness.RootPreprocessing
