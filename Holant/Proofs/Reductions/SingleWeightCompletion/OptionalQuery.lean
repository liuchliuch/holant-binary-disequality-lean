import Holant.Proofs.Reductions.SingleWeightCompletion.GraphProgram
import Holant.Proofs.Reductions.RootPreprocessing.Semantics


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.OptionalQuery
open Holant.Tractable
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open FixedGadgetSubstitution.Compiler RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (d : Fin s → ℕ)

def Accept (r : Input (s:=s) (a:=a)) : Prop := Balanced d r ∧ RootPreprocessing.Clean G r.val
abbrev Good := {r : Input (s:=s) (a:=a) // Accept G d r}
abbrev Target := ExactSignatureTables.Input s 1 (arity (a:=a) d)
abbrev sourceEncoding := validatedEncoding s 1 a
abbrev targetEncoding := validatedEncoding s 1 (arity (a:=a) d)
def goodEncoding : Encoding (Good G d) Bool where
  encode r := (sourceEncoding (s:=s) (a:=a)).encode r.val
  decode bits := do
    let r ← (sourceEncoding (s:=s) (a:=a)).decode bits
    if h : Accept G d r then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

def acceptComputes : Computes (sourceEncoding (s:=s) (a:=a)) encodingBoolBool
    (fun r => decide (Accept G d r)) :=
  congrComputes (ifComputes (ChargeProgram.balancedComputes d)
    (RootPreprocessing.cleanTestComputes G) (constantComputes _ encodingBoolBool false))
    (fun r => by by_cases h : Balanced d r <;> simp [Accept,h])
def select (r : Input (s:=s) (a:=a)) : Option (Good G d) :=
  if h : Accept G d r then some ⟨r,h⟩ else none
def selectComputes : Computes (sourceEncoding (s:=s) (a:=a))
    (optionEncoding (goodEncoding G d)) (select G d) := by
  let someWord := joinComputes
    (constantComputes (sourceEncoding (s:=s) (a:=a)) Frame.wordEncoding [true])
    (encodeComputes (sourceEncoding (s:=s) (a:=a)))
  let run := ifComputes (acceptComputes G d) someWord
    (constantComputes (sourceEncoding (s:=s) (a:=a)) Frame.wordEncoding [false])
  refine recode run id (fun _ => rfl) ?_
  intro r
  by_cases h : Accept G d r <;> simp [select,h,optionEncoding,goodEncoding,Frame.wordEncoding]

def goodQuery (r : Good G d) : Target (a:=a) d := CompletedGraph.query d r.val r.property.1
def goodQueryComputes : Computes (goodEncoding G d) (targetEncoding (a:=a) d) (goodQuery G d) :=
  recode (GraphProgram.rawComputes d) Subtype.val (fun _ => rfl)
    (fun r => congrArg RawClosedNetwork.encoding.encode (GraphProgram.raw_query d r.val r.property.1))
def query (r : Input (s:=s) (a:=a)) : Option (Target (a:=a) d) := (select G d r).map (goodQuery G d)
def computes : Computes (sourceEncoding (s:=s) (a:=a)) (optionEncoding (targetEncoding (a:=a) d)) (query G d) :=
  (selectComputes G d).andThen (OptionMap.computes (goodQueryComputes G d))

theorem rejected_provider :
    RunsExactly (OptionMap.machine (goodQueryComputes G d).machine).computer.step
      (Turing.initList (OptionMap.machine (goodQueryComputes G d).machine).computer [false])
      (Turing.haltList (OptionMap.machine (goodQueryComputes G d).machine).computer [false]) 2 :=
  OptionMap.none_exact (goodQueryComputes G d).machine

theorem reject_zero (hd : ∀ i, Signature.SingleLayer (G i) (d i))
    (r : Input (s:=s) (a:=a)) (h : ¬ Accept G d r) :
    (r.val.realize r.property G (fun _ => Signature.disequality)).denote Fin.elim0=0 := by
  by_cases hb : Balanced d r
  · exact RootPreprocessing.zero_value G r (fun hc => h ⟨hb,hc⟩)
  · exact reject_value G d hd r hb

theorem accepted_value (r : Good G d) :
    ((goodQuery G d r).val.realize (goodQuery G d r).property (table G d)
      (fun _ => Signature.disequality)).denote Fin.elim0 =
    (r.val.val.realize r.val.property G (fun _ => Signature.disequality)).denote Fin.elim0 :=
  CompletedGraph.query_value G d r.val r.property.1

/-- A zero signature can never occur in a query, even though the fixed indexed
alphabet deliberately retains the source index set and its duplicates. -/
theorem live_rows (r : Good G d) (v : Fin r.val.val.vertices.length) :
    table G d (r.val.val.signatureLabel r.val.property v) ≠ 0 := by
  apply (table_nonzero G d _).mpr
  exact (RootPreprocessing.clean_iff G r.val).mp r.property.2 _ (List.get_mem _ _) _

theorem emitted_rows_nonzero (r : Good G d) (row : RawVertex)
    (hm : row ∈ (goodQuery G d r).val.vertices) (hi : row.1<s) :
    table G d ⟨row.1,hi⟩ ≠ 0 := by
  change row ∈ (CompletedGraph.query d r.val r.property.1).val.vertices at hm
  rw [CompletedGraph.rows_exact] at hm
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hm
  exact live_rows G d r v

/-- Membership is asserted for the labels actually emitted, not only for an
unrelated catalogue of possible completed signatures. -/
theorem emitted_family (hd : ∀ i, Signature.SingleLayer (G i) (d i))
    (r : Good G d) (v : Fin (goodQuery G d r).val.vertices.length) :
    (⟨arity (a:=a) d ((goodQuery G d r).val.signatureLabel (goodQuery G d r).property v).val,
      table G d ((goodQuery G d r).val.signatureLabel (goodQuery G d r).property v)⟩ :
      AnySignature AlgebraicComplex) ∈ Tractable.completionFamily (sourceFamily G) := by
  let i := (goodQuery G d r).val.signatureLabel (goodQuery G d r).property v
  have hn : G i≠0 := (table_nonzero G d i).mp
    (emitted_rows_nonzero G d r _ (List.get_mem _ _) i.isLt)
  have hm : label G d i ∈ Set.range (fun j : {j : Fin s // G j≠0} => label G d j.val) :=
    ⟨⟨i,hn⟩,rfl⟩
  rw [nonzero_image d G hd] at hm
  simpa only [table_label] using hm

theorem nonzero_nullary_layer {f : Signature AlgebraicComplex 0} {e : ℕ}
    (hf : f ≠ 0) (he : Signature.SingleLayer f e) : e=0 := by
  have hn : f Fin.elim0 ≠ 0 := by
    intro hz
    apply hf
    funext x
    have hx : x=Fin.elim0 := Subsingleton.elim _ _
    simpa [hx] using hz
  simpa using (he.weight_of_nezero hn).symm

theorem nullary_slots {f : Signature AlgebraicComplex 0} {e : ℕ}
    (hf : f ≠ 0) (he : Signature.SingleLayer f e) : extra 0 e=0 := by
  rw [nonzero_nullary_layer hf he]
  rfl

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.OptionalQuery
