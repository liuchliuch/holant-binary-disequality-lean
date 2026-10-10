import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.FixedGadgetSubstitution.Raw
import Holant.Complexity.GraphPreprocessing.ComponentSelection.UnaryRange
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CountsPackageInterface

/-! All graph counts, ordered source rows and finite source labels are obtained
from the original validated raw encoding by actual parsing and scanning. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
abbrev Input (s b : ℕ) (arity : ℕ → ℕ) := {r : RawClosedNetwork // r.WellFormed s b arity}
abbrev Query (s b : ℕ) (arity : ℕ → ℕ) := Σ r : Input s b arity, Fin r.val.vertices.length
def queryEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (validatedEncoding s b arity) (fun r => OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
variable (s b : ℕ) (arity : ℕ → ℕ)
noncomputable def rowsComputes : Computes (validatedEncoding s b arity)
    (framedListEncoding vertexEncoding) (fun r => r.val.vertices) :=
  recode (Wiring.firstComputes (framedListEncoding vertexEncoding) (framedListEncoding encodingNatBool))
    (fun r => (r.val.vertices,r.val.edges)) (fun _ => rfl) (fun _ => rfl)
noncomputable def edgesComputes : Computes (validatedEncoding s b arity)
    (framedListEncoding encodingNatBool) (fun r => r.val.edges) :=
  recode (Wiring.secondComputes (framedListEncoding vertexEncoding) (framedListEncoding encodingNatBool))
    (fun r => (r.val.vertices,r.val.edges)) (fun _ => rfl) (fun _ => rfl)
noncomputable def countsComputes : Computes (validatedEncoding s b arity)
    (pairEncoding (validatedEncoding s b arity) (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))
    (fun r => (r,(r.val.vertices.length,r.val.edges.length))) :=
  recode CountsPackage.computes Subtype.val (fun _ => rfl) (fun _ => rfl)
noncomputable def vertexCountComputes : Computes (validatedEncoding s b arity)
    UnaryBinary.unaryEncoding (fun r => r.val.vertices.length) :=
  ((countsComputes s b arity).andThen (Wiring.secondComputes (validatedEncoding s b arity)
    (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))).andThen
    (Wiring.firstComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
noncomputable def edgeCountComputes : Computes (validatedEncoding s b arity)
    UnaryBinary.unaryEncoding (fun r => r.val.edges.length) :=
  ((countsComputes s b arity).andThen (Wiring.secondComputes (validatedEncoding s b arity)
    (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding))).andThen
    (Wiring.secondComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
noncomputable def sourceComputes : Computes (queryEncoding s b arity)
    (validatedEncoding s b arity) (fun x => x.1) :=
  recode (Wiring.firstComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
noncomputable def indexComputes : Computes (queryEncoding s b arity)
    UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
noncomputable def originalRowComputes : Computes (queryEncoding s b arity) vertexEncoding
    (fun x => x.1.val.vertices.get x.2) := by
  let prepare : Computes (queryEncoding s b arity) (ParentRowSelect.inputEncoding vertexEncoding)
      (fun x => ⟨x.1.val.vertices,x.2⟩) :=
    recode (pairComputes ((sourceComputes s b arity).andThen (rowsComputes s b arity))
      (indexComputes s b arity)) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ParentRowSelect.computes vertexEncoding)
def sourceLabel (x : Query s b arity) : Fin s :=
  ⟨(x.1.val.vertices.get x.2).1,(x.1.property.1 x.2).1⟩
noncomputable def labelComputes : Computes (queryEncoding s b arity)
    (SignatureLabel.binaryFinEncoding s) (sourceLabel s b arity) :=
  recode ((originalRowComputes s b arity).andThen
    (recode (Wiring.firstComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))) id (fun _ => rfl) (fun _ => rfl)
noncomputable def labelRecodeComputes {B : Type} (e : Encoding B Bool) (f : Fin s → B) :
    Computes (queryEncoding s b arity) e (fun x => f (sourceLabel s b arity x)) :=
  (labelComputes s b arity).andThen
    (FiniteRecode.computes (SignatureLabel.binaryFinEncoding s) e f s.size
      (SignatureLabel.binaryFinEncoding_length_le s))
theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp
theorem finListEncoding (n : ℕ) (xs : List (Fin n)) :
    framedListEncode UnaryBinary.unaryEncoding (xs.map Fin.val) =
      framedListEncode (OccurrenceLabel.unaryPortEncoding n) xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons,framedListEncode,ih]; rfl
def allQueriesEncoding := ContextFlatMap.inputEncoding (validatedEncoding s b arity)
  (fun r => OccurrenceLabel.unaryPortEncoding r.val.vertices.length)
noncomputable def allQueriesComputes : Computes (validatedEncoding s b arity) (allQueriesEncoding s b arity)
    (fun r => ⟨r,List.finRange r.val.vertices.length⟩) :=
  recode (pairComputes (identityComputes (validatedEncoding s b arity))
    ((vertexCountComputes s b arity).andThen ComponentSelection.UnaryRange.computes))
    id (fun _ => rfl) (fun r => by
      change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
      rw [←finRange_values,finListEncoding]
      rfl)
/-- Every original vertex is visited in its literal order, including nullary rows. -/
noncomputable def allRowsFlatMapComputes (f : Query s b arity → List Bool)
    (w : Computes (queryEncoding s b arity) Frame.wordEncoding f) :
    Computes (validatedEncoding s b arity) Frame.wordEncoding
      (fun r => (List.finRange r.val.vertices.length).flatMap (fun v => f ⟨r,v⟩)) :=
  (allQueriesComputes s b arity).andThen
    (ContextFlatMap.computes (validatedEncoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.vertices.length) f w)
end Holant.Complexity.FixedGadgetSubstitution.Compiler
