import Holant.Proofs.Traversal.ArityTwo.MatrixEmission


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.EndpointEmission
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)
abbrev Query := RawPortQuery.Input s b arity
abbrev queryEncoding := RawPortQuery.encoding s b arity
abbrev Scan := Σ x : Query s b arity, Fin x.1.val.edges.length
def scanEncoding := sigmaEncoding (queryEncoding s b arity)
  (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.edges.length)

def contextComputes : Computes (scanEncoding s b arity) (queryEncoding s b arity) Sigma.fst :=
  recode (Wiring.firstComputes (queryEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def indexComputes : Computes (scanEncoding s b arity) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (queryEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def candidateQuery (x : Scan s b arity) : EdgeWord.Input s b arity := ⟨x.1.1,x.2⟩
def candidateComputes : Computes (scanEncoding s b arity) (EdgeWord.inputEncoding s b arity)
    (candidateQuery s b arity) :=
  recode (pairComputes
    ((contextComputes s b arity).andThen (RawPortQuery.sourceComputes s b arity))
    (indexComputes s b arity)) id (fun _ => rfl) (fun _ => rfl)

def endpointComputes := (contextComputes s b arity).andThen (RawPortQuery.endpointComputes s b arity)

def matchesComputes : Computes (scanEncoding s b arity) encodingBoolBool
    (fun x => decide (x.2.val = x.1.2.1.val)) :=
  (pairComputes ((indexComputes s b arity).andThen UnaryBinary.computes)
    ((endpointComputes s b arity).andThen
      (recode (Wiring.firstComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl)))).andThen
        (equalComputes encodingNatBool)

def sideComputes : Computes (scanEncoding s b arity) encodingBoolBool (fun x => x.1.2.2) :=
  (endpointComputes s b arity).andThen
    (recode (Wiring.secondComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl))

def candidateWord (x : Scan s b arity) :=
  MatrixEmission.edgeWord s b arity edges codec x.1.2.2 (candidateQuery s b arity x)

def wordComputes : Computes (scanEncoding s b arity) Frame.wordEncoding
    (candidateWord s b arity edges codec) :=
  congrComputes (ifComputes (sideComputes s b arity)
    ((candidateComputes s b arity).andThen (MatrixEmission.edgeComputes s b arity edges codec true))
    ((candidateComputes s b arity).andThen (MatrixEmission.edgeComputes s b arity edges codec false)))
    (fun x => by cases hb : x.1.2.2 <;> simp [candidateWord, hb])

def chunk (x : Scan s b arity) : List Bool :=
  if x.2.val = x.1.2.1.val then candidateWord s b arity edges codec x else []

def chunkComputes : Computes (scanEncoding s b arity) Frame.wordEncoding
    (chunk s b arity edges codec) :=
  congrComputes (ifComputes (matchesComputes s b arity) (wordComputes s b arity edges codec)
    (constantComputes (scanEncoding s b arity) Frame.wordEncoding [])) (fun _ => by simp [chunk])

def prepare : Computes (queryEncoding s b arity)
    (ContextFlatMap.inputEncoding (queryEncoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.edges.length))
    (fun x => ⟨x,List.finRange x.1.val.edges.length⟩) :=
  recode (pairComputes (identityComputes (queryEncoding s b arity))
    (((RawPortQuery.sourceComputes s b arity).andThen (edgeCountComputes s b arity)).andThen
      ComponentSelection.UnaryRange.computes)) id (fun _ => rfl) (fun x => by
        change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
        rw [← finRange_values,finListEncoding]
        rfl)

theorem select_flatMap {I : Type} [DecidableEq I] (f : I → List Bool) (q : I)
    (xs : List I) (hn : xs.Nodup) (hq : q ∈ xs) :
    xs.flatMap (fun i => if i = q then f i else []) = f q := by
  induction xs with
  | nil => simp at hq
  | cons i xs ih =>
    obtain ⟨hin,ht⟩ := List.nodup_cons.mp hn
    by_cases hi : i = q
    · subst i
      have hz : xs.flatMap (fun i => if i = q then f i else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro i hm
        have hne : i ≠ q := by intro he; subst i; exact hin hm
        simp [hne]
      simp [hz]
    · have hm : q ∈ xs := (List.mem_cons.mp hq).resolve_left (Ne.symm hi)
      simpa [hi] using ih ht hm

def value (x : Query s b arity) := MatrixEmission.word codec
  (matrixStep (orient x.2.2 (edges (x.1.val.edgeLabel x.1.property x.2.1))))

theorem scan_value (x : Query s b arity) :
    (List.finRange x.1.val.edges.length).flatMap
      (fun e => chunk s b arity edges codec ⟨x,e⟩) = value s b arity edges codec x := by
  have h := select_flatMap
    (fun e => candidateWord s b arity edges codec ⟨x,e⟩) x.2.1
    (List.finRange x.1.val.edges.length) (List.nodup_finRange _) (by simp)
  simpa [chunk,Fin.ext_iff,value,candidateWord,candidateQuery,MatrixEmission.edgeWord] using h

def computes : Computes (queryEncoding s b arity) Frame.wordEncoding (value s b arity edges codec) :=
  congrComputes ((prepare s b arity).andThen
    (ContextFlatMap.computes (queryEncoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.1.val.edges.length)
      (chunk s b arity edges codec) (chunkComputes s b arity edges codec)))
    (scan_value s b arity edges codec)

theorem primitive_bound (x : Query s b arity) :
    let w := computes s b arity edges codec
    primitiveCost w.machine (w.outputs x).steps
      (some (Turing.initList w.machine.computer ((queryEncoding s b arity).encode x))) ≤
        (primitivePolynomial w).eval ((queryEncoding s b arity).encode x).length :=
  computes_primitive_cost (computes s b arity edges codec) x

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.EndpointEmission
