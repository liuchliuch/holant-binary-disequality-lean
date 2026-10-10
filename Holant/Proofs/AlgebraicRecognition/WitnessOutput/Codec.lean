import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.API
import Holant.Proofs.Algorithms.TransformRecognition.StructuredWitness


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
open Computability Holant.Algebraic
open Holant.Complexity Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open PositiveCertificateMachine ComplexIsolation
open Holant.OneHot.StackProgram.GraphLabelEncoding

abbrev Quad := (List ℚ × List ℚ) × (List ℚ × List ℚ)
abbrev quadEncoding := pairEncoding
  (pairEncoding CommonFieldMachine.coordinatesEncoding CommonFieldMachine.coordinatesEncoding)
  (pairEncoding CommonFieldMachine.coordinatesEncoding CommonFieldMachine.coordinatesEncoding)

def quad (f : Bool → Bool → List ℚ) : Quad :=
  ((f false false, f false true), (f true false, f true true))

def Quad.entry (q : Quad) (u v : Bool) : List ℚ :=
  if u then (if v then q.2.2 else q.2.1) else (if v then q.1.2 else q.1.1)

@[simp] theorem quad_entry (f : Bool → Bool → List ℚ) (u v : Bool) :
    (quad f).entry u v = f u v := by
  cases u <;> cases v <;> rfl

structure Output where
  root : RootCode
  relation : List ℚ
  matrix : Quad
  inverse : Quad
  scalars : List (List ℚ)
  «variables» : List (List ℚ)

abbrev Wire := RootCode × (List ℚ × (Quad × (Quad ×
  (List (List ℚ) × List (List ℚ)))))
abbrev wireEncoding := pairEncoding CertificateMachine.rootEncoding
  (pairEncoding CommonFieldMachine.coordinatesEncoding
    (pairEncoding quadEncoding (pairEncoding quadEncoding
      (pairEncoding vectorsEncoding vectorsEncoding))))

def Output.wire (o : Output) : Wire :=
  (o.root, o.relation, o.matrix, o.inverse, o.scalars, o.variables)
def Output.unwire (w : Wire) : Output :=
  ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2⟩

def outputEncoding : Encoding Output Bool where
  encode o := wireEncoding.encode o.wire
  decode w := (wireEncoding.decode w).map Output.unwire
  decode_encode o := by
    change (wireEncoding.decode (wireEncoding.encode o.wire)).map Output.unwire = some o
    rw [wireEncoding.decode_encode]
    cases o
    rfl

abbrev resultEncoding := optionEncoding outputEncoding
abbrev outputsEncoding := framedListEncoding outputEncoding

def matrixEntry (r : Request) (u v : Bool) : List ℚ :=
  r.values.getD (MatrixWitness.index u v).val []
def adjugateEntry (r : Request) (u v : Bool) : List ℚ :=
  if u = v then matrixEntry r (!u) (!v)
  else CommonFieldMachine.Coordinates.scale (-1) (matrixEntry r u v)
def inverseEntry (r : Request) (u v : Bool) : List ℚ :=
  CommonFieldMachine.Coordinates.mul r.family.relation (r.values.getD 4 [])
    (adjugateEntry r u v)
def scalarValues (r : Request) : List (List ℚ) :=
  (List.range (r.values.length - 5)).map (fun i => r.values.getD (5 + i) [])

def emit (r : Request) : Output :=
  ⟨r.certificate.rootCode (relationPolynomial r.family.relation),
    r.family.relation, quad (matrixEntry r), quad (inverseEntry r), scalarValues r, r.values⟩

def ofStructured {d k : ℕ} (o : StructuredWitness.Output d k)
    (v : MatrixWitness.Candidate d k) : Output :=
  ⟨o.root, List.ofFn o.relation,
    quad (fun u w => List.ofFn (o.coordinates.matrix u w)),
    quad (fun u w => List.ofFn (o.coordinates.inverse u w)),
    List.ofFn (fun i => List.ofFn (o.coordinates.scalars i)),
    List.ofFn (fun i => List.ofFn (v i))⟩

def ofCandidate {m k : ℕ} (a : PositiveWitnessSearch.Candidate m k) : Output :=
  ofStructured (StructuredWitness.emit a) a.1.2.2.2.2

@[simp] theorem ofCandidate_matrix {m k : ℕ} (a : PositiveWitnessSearch.Candidate m k)
    (u v : Bool) :
    (ofCandidate a).matrix.entry u v = List.ofFn (MatrixWitness.matrixCode a.1.2.2.2.2 u v) :=
  quad_entry _ u v

@[simp] theorem ofCandidate_inverse {m k : ℕ} (a : PositiveWitnessSearch.Candidate m k)
    (u v : Bool) :
    (ofCandidate a).inverse.entry u v =
      List.ofFn (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v) := quad_entry _ u v

@[simp] theorem ofCandidate_variables {m k : ℕ} (a : PositiveWitnessSearch.Candidate m k) :
    (ofCandidate a).variables = List.ofFn (fun i => List.ofFn (a.1.2.2.2.2 i)) := rfl

theorem matrixEntry_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k)
    (u v : Bool) :
    matrixEntry (fromSource target S a) u v =
      List.ofFn (MatrixWitness.matrixCode a.1.2.2.2.2 u v) := by
  exact getD_ofFn (fun i => List.ofFn (a.1.2.2.2.2 i))
    (Fin.castAdd k (MatrixWitness.index u v)) []

theorem inverseEntry_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k)
    (u v : Bool) :
    inverseEntry (fromSource target S a) u v =
      List.ofFn (MatrixWitness.inverseCode a.1.2.1 a.1.2.2.2.2 u v) := by
  have hz : (fromSource target S a).values.getD 4 [] =
      List.ofFn (a.1.2.2.2.2 (Fin.castAdd k (4 : Fin 5))) :=
    getD_ofFn (fun i => List.ofFn (a.1.2.2.2.2 i)) (Fin.castAdd k (4 : Fin 5)) []
  have hadj : adjugateEntry (fromSource target S a) u v =
      List.ofFn (if u = v then MatrixWitness.matrixCode a.1.2.2.2.2 (!u) (!v)
        else -MatrixWitness.matrixCode a.1.2.2.2.2 u v) := by
    by_cases huv : u = v
    · simp only [adjugateEntry, if_pos huv, matrixEntry_fromSource]
    · simp only [adjugateEntry, if_neg huv, matrixEntry_fromSource,
        CommonFieldMachine.Coordinates.scale_ofFn, neg_one_smul]
  rw [inverseEntry, hz, hadj]
  change CommonFieldMachine.Coordinates.mul (List.ofFn a.1.2.1) _ _ = _
  rw [CommonFieldMachine.Coordinates.mul_ofFn] <;> rfl

theorem scalarValues_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    scalarValues (fromSource target S a) =
      List.ofFn (fun i : Fin k => List.ofFn (a.1.2.2.2.2 (Fin.natAdd 5 i))) := by
  change CommonFieldMachine.Coordinates.tab
    ((List.ofFn (fun i => List.ofFn (a.1.2.2.2.2 i))).length - 5)
    (fun i => (List.ofFn (fun j => List.ofFn (a.1.2.2.2.2 j))).getD (5+i) []) = _
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [CommonFieldMachine.Coordinates.tab_ofFn]
  congr 1
  funext i
  exact getD_ofFn (fun j => List.ofFn (a.1.2.2.2.2 j)) (Fin.natAdd 5 i) []

/-- Equality of all output fields, including the literal original root code,
both matrices, every scalar slot and every original variable coordinate. -/
theorem emit_fromSource {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    emit (fromSource target S a) = ofCandidate a := by
  have hr : relationPolynomial (fromSource target S a).family.relation =
      Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.relationCode a.1.2.1 :=
    relationPolynomial_ofFn _
  simp only [emit, ofCandidate, ofStructured, StructuredWitness.emit,
    MatrixWitness.output, quad, hr, matrixEntry_fromSource,
    inverseEntry_fromSource, scalarValues_fromSource] <;> rfl

theorem output_faithful : Function.Injective outputEncoding.encode :=
  outputEncoding.encode_injective

theorem source_bytes {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    outputEncoding.encode (emit (fromSource target S a)) =
      outputEncoding.encode (ofCandidate a) := congrArg outputEncoding.encode (emit_fromSource target S a)

theorem source_roundtrip {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (a : PositiveWitnessSearch.Candidate m k) :
    outputEncoding.decode (outputEncoding.encode (emit (fromSource target S a))) = some (ofCandidate a) := by
  rw [outputEncoding.decode_encode, emit_fromSource]

end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput
