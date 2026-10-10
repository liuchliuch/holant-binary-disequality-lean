import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Programs


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open ComplexIsolation

def Valid (c : RootCode) : Prop := ∃ z : ℂ, c.Represents z

def candidateAt (c : RootCode) (q : Code.Poly) (n : ℕ) : Option Evidence :=
  match Encodable.decode (α := Evidence) n with
  | none => none
  | some e => if check c q e then some e else none

theorem candidateAt_some {c : RootCode} {q : Code.Poly} {n : ℕ} {e : Evidence}
    (h : candidateAt c q n=some e) : check c q e=true := by
  cases hd : Encodable.decode (α := Evidence) n with
  | none => simp [candidateAt,hd] at h
  | some a =>
    cases hc : check c q a with
    | false => simp [candidateAt,hd,hc] at h
    | true =>
      have ha : a=e := by simpa [candidateAt,hd,hc] using h
      simpa only [ha] using hc

theorem candidateAt_encode (c : RootCode) (q : Code.Poly) (e : Evidence)
    (he : check c q e=true) : candidateAt c q (Encodable.encode e)=some e := by
  simp [candidateAt,Encodable.encodek,he]

theorem candidate_exists (c : RootCode) (q : Code.Poly) (hv : Valid c) :
    ∃ n, (candidateAt c q n).isSome=true := by
  obtain ⟨z,hz⟩ := hv
  obtain ⟨e,he⟩ := check_complete hz q
  exact ⟨Encodable.encode e,by rw [candidateAt_encode c q e he]; rfl⟩

def searchIndex (c : RootCode) (q : Code.Poly) (hv : Valid c) : ℕ :=
  Nat.find (candidate_exists c q hv)

def zeroPolynomial (c : RootCode) (q : Code.Poly) (hv : Valid c) : Bool :=
  ((candidateAt c q (searchIndex c q hv)).map Evidence.zero).getD false

theorem searchIndex_spec (c : RootCode) (q : Code.Poly) (hv : Valid c) :
    (candidateAt c q (searchIndex c q hv)).isSome=true := by
  change (candidateAt c q (Nat.find (candidate_exists c q hv))).isSome=true
  exact Nat.find_spec (candidate_exists c q hv)

theorem searchIndex_le (c : RootCode) (q : Code.Poly) (hv : Valid c) (n : ℕ)
    (hn : (candidateAt c q n).isSome=true) : searchIndex c q hv≤n := Nat.find_min' _ hn

/-- Complete comparison at the root named by the unchanged RootCode, including
reducible and repeated input relations. There is no zero-correctness premise. -/
theorem zeroPolynomial_iff (c : RootCode) (q : Code.Poly) (hv : Valid c)
    (z : ℂ) (hz : c.Represents z) :
    zeroPolynomial c q hv=true ↔ Polynomial.aeval z q.polynomial=0 := by
  have hs := searchIndex_spec c q hv
  cases ha : candidateAt c q (searchIndex c q hv) with
  | none => simp only [ha,Option.isSome_none,Bool.false_eq_true] at hs
  | some e =>
    simpa only [zeroPolynomial,ha,Option.map_some,Option.getD_some] using
      check_sound hz (candidateAt_some ha)

def zeroList (c : RootCode) (v : List ℚ) (hv : Valid c) : Bool :=
  zeroPolynomial c (Code.dense v) hv

theorem zeroList_iff (c : RootCode) (v : List ℚ) (hv : Valid c)
    (z : ℂ) (hz : c.Represents z) :
    zeroList c v hv=true ↔ BranchConsumers.decodeList z v=0 := by
  simpa only [zeroList,Code.dense_correct] using zeroPolynomial_iff c (Code.dense v) hv z hz

namespace Scan
abbrev Context := RootCode × Code.Poly
abbrev contextEncoding := pairEncoding CertificateMachine.rootEncoding CertificateMachine.polynomialEncoding
abbrev evidenceListEncoding := framedListEncoding evidenceEncoding
abbrev inputEncoding := pairEncoding contextEncoding evidenceListEncoding
abbrev valuesEncoding := framedListEncoding encodingBoolBool
abbrev resultEncoding := Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding encodingBoolBool

def checked (x : Context) (e : Evidence) : List Bool :=
  if check x.1 x.2 e then [e.zero] else []
def values (x : Context) (es : List Evidence) : List Bool := es.flatMap (checked x)
def first (x : Context) (es : List Evidence) : Option Bool := (values x es).head?

theorem mem_values {x : Context} {es : List Evidence} {b : Bool} :
    b ∈ values x es ↔ ∃ e ∈ es, check x.1 x.2 e=true ∧ e.zero=b := by
  change b ∈ es.flatMap (checked x) ↔ _
  constructor
  · intro hb
    obtain ⟨e,he,hb⟩ := List.mem_flatMap.mp hb
    by_cases hc : check x.1 x.2 e=true
    · rw [checked,if_pos hc] at hb
      exact ⟨e,he,hc,(List.mem_singleton.mp hb).symm⟩
    · rw [checked,if_neg hc] at hb
      exact False.elim (List.not_mem_nil hb)
  · rintro ⟨e,he,hc,htag⟩
    refine List.mem_flatMap.mpr ⟨e,he,?_⟩
    rw [checked,if_pos hc]
    exact List.mem_singleton.mpr htag.symm

theorem first_sound {c : RootCode} {q : Code.Poly} {es : List Evidence} {b : Bool}
    {z : ℂ} (hz : c.Represents z) (hb : first (c,q) es=some b) :
    b=true ↔ Polynomial.aeval z q.polynomial=0 := by
  have hh : (values (c,q) es).head?=some b := hb
  have hhead : b∈(values (c,q) es).head? := by rw [hh]; simp
  have hmem : b∈values (c,q) es := List.mem_of_mem_head? hhead
  obtain ⟨e,_,he,htag⟩ := mem_values.mp hmem
  simpa only [htag] using check_sound hz he

noncomputable section
def selectChecked : Computes (pairEncoding encodingBoolBool encodingBoolBool) valuesEncoding
    (fun p : Bool × Bool => if p.1 then [p.2] else []) :=
  ifComputes (Wiring.firstComputes _ _)
    ((Wiring.secondComputes _ _).andThen (NegativeCertificateMachine.Lists.singleton encodingBoolBool))
    (constantComputes _ valuesEncoding [])

def checkedExecutes : Executes (pairEncoding contextEncoding evidenceEncoding) valuesEncoding
    (fun p => checked p.1 p.2) := by
  let context := Wiring.firstComputes contextEncoding evidenceEncoding
  let e := Wiring.secondComputes contextEncoding evidenceEncoding
  let c := context.andThen (Wiring.firstComputes _ _)
  let q := context.andThen (Wiring.secondComputes _ _)
  let prepare := pairComputes c (pairComputes q e)
  let accepted := (Executes.ofComputes prepare).comp ReturnedRootBranchSelection.executes
  exact (accepted.pair (Executes.ofComputes (e.andThen evidenceTag))).comp
    (Executes.ofComputes selectChecked)

def valuesExecutes : Executes inputEncoding valuesEncoding (fun p => values p.1 p.2) :=
  ((Executes.mapList contextEncoding evidenceEncoding valuesEncoding checked checkedExecutes).comp
    (Executes.ofComputes (WireLists.flatten encodingBoolBool))).congr
      (fun p => by simp only [values,List.flatMap_def])

def someComputes : Computes encodingBoolBool resultEncoding (fun b => some b) :=
  recode (joinComputes (constantComputes encodingBoolBool Frame.wordEncoding [true])
    (encodeComputes encodingBoolBool)) id (fun _ => rfl) (fun _ => rfl)
def headComputes : Computes valuesEncoding resultEncoding List.head? := by
  let tagged := WireLists.mapComputes encodingBoolBool resultEncoding (fun b => some b) someComputes
  let first := tagged.andThen (getDComputes resultEncoding 0 none)
  exact congrComputes first (fun xs => by cases xs <;> rfl)
def executes : Executes inputEncoding resultEncoding (fun p => first p.1 p.2) :=
  valuesExecutes.comp (Executes.ofComputes headComputes)
def outputs (x : Context) (es : List Evidence) : TM2OutputsInTime executes.machine.computer
    (inputEncoding.encode (x,es)) (some (resultEncoding.encode (first x es))) (executes.cost (x,es)) :=
  executes.outputs (x,es)
end
end Scan
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
