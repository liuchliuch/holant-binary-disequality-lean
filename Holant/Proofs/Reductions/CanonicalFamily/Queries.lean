import Holant.Proofs.Reductions.CanonicalFamily.Alphabet
import Holant.Proofs.Reductions.RootPreprocessing.ScalarProduct


noncomputable section
namespace Holant.LocalDrafts.Hardness.CanonicalFamily
open Holant.Tractable Holant.Complexity.GraphPreprocessing
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false

namespace Relabel
variable {s t : ℕ} {a c : ℕ → ℕ} (σ : Fin s → Fin t)
def label (i : ℕ) : ℕ := if hi : i < s then (σ ⟨i,hi⟩).val else 0
@[simp] theorem label_fin (i : Fin s) : label σ i.val = (σ i).val := by simp [label,i.isLt]
def row (v : RawVertex) : RawVertex := (label σ v.1,v.2)
def raw (r : RawClosedNetwork) : RawClosedNetwork := ⟨r.vertices.map (row σ),r.edges⟩
variable (ha : ∀ i : Fin s, c (σ i).val = a i.val)

include ha in
theorem wellFormed (r : ExactSignatureTables.Input s 1 a) : (raw σ r.val).WellFormed t 1 c := by
  have hr := (RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property
  apply (RawGrouping.wellFormed_iff_members _ _ _ _).mpr
  refine ⟨?_,hr.2.1,?_⟩
  · intro v hv
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp hv
    have ho := hr.1 old hm
    let i : Fin s := ⟨old.1,ho.1⟩
    change label σ i.val < t ∧ old.2.length = c (label σ i.val)
    rw [label_fin,ha]
    exact ⟨(σ i).isLt,ho.2⟩
  · simpa [raw,endpoints,expectedEndpoints,row,List.map_map,Function.comp_def] using hr.2.2

def input (r : ExactSignatureTables.Input s 1 a) : ExactSignatureTables.Input t 1 c :=
  ⟨raw σ r.val,wellFormed σ ha r⟩

def computes : Computes (validatedEncoding s 1 a) (validatedEncoding t 1 c) (input σ ha) := by
  let one : Computes (queryEncoding s 1 a) vertexEncoding
      (fun x => ((σ (sourceLabel s 1 a x)).val,(x.1.val.vertices.get x.2).2)) :=
    recode (pairComputes (labelRecodeComputes s 1 a encodingNatBool (fun i => (σ i).val))
      (GroupingMachine.rowPortsComputes s 1 a)) id (fun _ => rfl) (fun _ => rfl)
  let provider : Computes (queryEncoding s 1 a) Frame.wordEncoding
      (fun x => entries vertexEncoding [row σ (x.1.val.vertices.get x.2)]) :=
    congrComputes (one.andThen (entryComputes vertexEncoding)) (fun x => by
      have hi : (x.1.val.vertices.get x.2).1 < s := (x.1.property.1 x.2).1
      have hi' : (x.1.val.vertices[x.2.val]).1 < s := hi
      simp [entries,row,label,sourceLabel,hi'])
  let rows := RootPreprocessing.RowProgram.computes (fun v => [row σ v]) provider
  refine recode (pairComputes rows (edgesComputes s 1 a)) id (fun _ => rfl) ?_
  intro r
  simp only [← List.map_eq_flatMap] <;> rfl

theorem vertices_length (r : RawClosedNetwork) : (raw σ r).vertices.length = r.vertices.length := by
  simp [raw]
theorem ordered_ports (r : RawClosedNetwork) :
    (raw σ r).vertices.map Prod.snd = r.vertices.map Prod.snd := by simp [raw,row,List.map_map,Function.comp_def]
theorem edges (r : RawClosedNetwork) : (raw σ r).edges = r.edges := rfl

end Relabel

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
abbrev Input := ExactSignatureTables.Input s 1 a
abbrev KeyInput := ExactSignatureTables.Input (count G) 1 (arity G)
abbrev sourceEncoding := validatedEncoding s 1 a
abbrev keyEncoding := validatedEncoding (count G) 1 (arity G)
def forwardQuery : Input (s:=s) (a:=a) → KeyInput G := Relabel.input (toKey G) (arity_toKey G)
def backwardQuery : KeyInput G → Input (s:=s) (a:=a) :=
  Relabel.input (selected G) (fun j => (arity_selected G j).symm)
def forwardComputes : Computes (sourceEncoding (s:=s) (a:=a)) (keyEncoding G) (forwardQuery G) :=
  Relabel.computes (toKey G) (arity_toKey G)
def backwardComputes : Computes (keyEncoding G) (sourceEncoding (s:=s) (a:=a)) (backwardQuery G) :=
  Relabel.computes (selected G) (fun j => (arity_selected G j).symm)

end Holant.LocalDrafts.Hardness.CanonicalFamily
