import Holant.Proofs.Reductions.RootPreprocessing.Programs
import Holant.Complexity.FixedFieldMachines.RawGraphEvaluator.Source


noncomputable section
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler RawClosedNetwork ExactSignatureTables
open UniversalPairReduction.Surgery
open Holant.OneHot.StackProgram.GraphLabelEncoding
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace OccurrenceProduct
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K d) (c : Fin s → K)

def total (i : ℕ) : K := if hi : i < s then c ⟨i,hi⟩ else 0
def value (r : RawClosedNetwork) : K := (r.vertices.map (fun row => total c row.1)).prod
def raw (r : RawClosedNetwork) : RawClosedNetwork := ⟨r.vertices.map (fun row => (row.1,[])),[]⟩
def coeff : CoefficientIndex s 1 (fun _ => 0) → Fin d → ℚ
  | .inl ⟨i,_⟩ => F.decode.symm (c i)
  | .inr (_,u,v) => F.decode.symm (Signature.disequality u v)

theorem wellFormed (r : Input (s:=s) (a:=a)) :
    (raw r.val).WellFormed s 1 (fun _ => 0) := by
  apply (Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members
    _ _ _ _).mpr
  refine ⟨?_,by simp [raw],by simp [raw,endpoints,expectedEndpoints]⟩
  intro row hm
  change row ∈ r.val.vertices.map (fun row => (row.1,[])) at hm
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hm
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hold
  exact ⟨by simpa only [hi] using (r.property.1 i).1,rfl⟩

def graph (r : Input (s:=s) (a:=a)) : GraphListCompiler.Input s 1 (fun _ => 0) :=
  ⟨raw r.val,wellFormed r⟩
theorem valid (r : Input (s:=s) (a:=a)) : RawGraphEvaluator.Valid F (coeff F c) (graph r) := by
  constructor
  · intro v w hw
    have hz : Holant.weight w = 0 := by
      simp [Holant.weight,RawGraphEvaluator.network,RawClosedNetwork.realize,
        RawClosedNetwork.shape]
    omega
  · intro e
    exact Fin.elim0 e

def input (r : Input (s:=s) (a:=a)) : RawGraphEvaluator.Input F (coeff F c) :=
  ⟨graph r,valid F c r⟩

theorem exact_value (r : Input (s:=s) (a:=a)) :
    RawGraphEvaluator.value F (coeff F c) (graph r) = value c r.val := by
  unfold RawGraphEvaluator.value RawGraphEvaluator.network
  simp only [coeff,LinearEquiv.apply_symm_apply]
  rw [Choice.denote_eq_evaluate]
  simp [Choice.evaluate,Choice.weight,Choice.rowValue,Choice.table,
    graph,raw,value,total,List.map_map,Function.comp_def]

def rawComputes : Computes (sourceEncoding (s:=s) (a:=a)) RawClosedNetwork.encoding
    (fun r => raw r.val) := by
  let rows := RowProgram.computes (fun row : RawVertex => [(row.1,[])])
    (labelRecodeComputes s 1 a Frame.wordEncoding
      (fun i => entries vertexEncoding [(i.val,[])]))
  refine recode (pairComputes rows (constantComputes _ (framedListEncoding encodingNatBool) []))
    id (fun _ => rfl) ?_
  intro r
  simp only [← List.map_eq_flatMap] <;> rfl

def inputComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (RawGraphEvaluator.inputEncoding F (coeff F c)) (input F c) :=
  recode rawComputes id (fun _ => rfl) (fun _ => rfl)

def computes : Computes (sourceEncoding (s:=s) (a:=a)) F.encoding
    (fun r => value c r.val) :=
  congrComputes ((inputComputes F c).andThen (RawGraphEvaluator.computes F (coeff F c)))
    (exact_value F c)

@[simp] theorem value_empty : value c ⟨[],[]⟩ = 1 := rfl
theorem value_cons (row : RawVertex) (rows : List RawVertex) (edges : List ℕ) :
    value c ⟨row::rows,edges⟩ = total c row.1 * value c ⟨rows,edges⟩ := rfl

end OccurrenceProduct

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def scalarLabel (i : Fin s) : sourceField G :=
  if a i.val = 0 then fieldCoefficient (sourceCoefficient G) (.inl ⟨i,fun _ => false⟩) else 1
def scalarNat (i : ℕ) : AlgebraicComplex :=
  if hi : i < s then if a i = 0 then G ⟨i,hi⟩ (fun _ => false) else 1 else 0
def scalar (r : RawClosedNetwork) : sourceField G := OccurrenceProduct.value (scalarLabel G) r
def context (r : Input (s:=s) (a:=a)) : sourceField G := if Clean G r.val then scalar G r.val else 0

theorem scalar_coe (r : RawClosedNetwork) :
    (scalar G r : AlgebraicComplex) = (r.vertices.map (fun row => scalarNat G row.1)).prod := by
  unfold scalar OccurrenceProduct.value
  change (sourceField G).subtype ((r.vertices.map (fun row => OccurrenceProduct.total (scalarLabel G) row.1)).prod) = _
  rw [map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro row _
  by_cases hi : row.1 < s <;> by_cases ha : a row.1 = 0 <;>
    simp [OccurrenceProduct.total,scalarLabel,scalarNat,hi,ha,sourceCoefficient,
      fieldCoefficient,Holant.LocalDrafts.MainChain.OriginalFamily.coefficient] <;> rfl

def scalarComputes : Computes (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (fun r => scalar G r.val) := OccurrenceProduct.computes (sourcePresentation G) (scalarLabel G)

/-- This scalar provider is total even on zero inputs. Eager scalar computation
is safe; the potentially inapplicable graph provider stays inside OptionMap. -/
def contextComputes : Computes (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (context G) :=
  congrComputes (UniversalPairReduction.SmoothingCompiler.ifComputes (cleanTestComputes G)
    (scalarComputes G) (constantComputes _ (sourcePresentation G).encoding 0))
    (fun r => by simp [context])

end Holant.LocalDrafts.Hardness.RootPreprocessing
