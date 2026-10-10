import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Original
import Holant.Proofs.Algorithms.TransformRecognition.OriginalProductSystem
import Holant.Proofs.Algorithms.TransformRecognition.OriginalLocalAffineSystem
import Holant.Proofs.Tractability.AffineMachine.DensePrograms


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers
open Holant Holant.Tractable Holant.Algebraic Computability
open Holant.Complexity FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open scoped BigOperators

abbrev Plan := List (List ℕ)
abbrev Groups := List (List (List ℚ))
abbrev indicesEncoding := framedListEncoding encodingNatBool
abbrev planEncoding := framedListEncoding indicesEncoding
abbrev groupsEncoding := framedListEncoding PositiveCertificateMachine.vectorsEncoding
abbrev Packet := Output × (Plan × Groups)
abbrev packetEncoding := pairEncoding outputEncoding (pairEncoding planEncoding groupsEncoding)
abbrev packetResultEncoding := Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding packetEncoding

def select (o : Output) (is : List ℕ) : List (List ℚ) :=
  is.map (fun i => o.variables.getD i [])
def project (p : Output × Plan) : Packet :=
  (p.1,p.2,p.2.map (select p.1))
def consume (p : Option Output × Plan) : Option Packet :=
  p.1.map (fun o => project (o,p.2))

@[simp] theorem project_payload (o : Output) (p : Plan) : (project (o,p)).1=o := rfl
@[simp] theorem project_plan (o : Output) (p : Plan) : (project (o,p)).2.1=p := rfl
@[simp] theorem consume_none (p : Plan) : consume (none,p)=none := rfl
@[simp] theorem consume_some (o : Output) (p : Plan) :
    consume (some o,p)=some (project (o,p)) := rfl

theorem select_ofCandidate {m k t : ℕ} (c : PositiveWitnessSearch.Candidate m k)
    (is : Fin t → Fin (5+k)) :
    select (ofCandidate c) (List.ofFn (fun i => (is i).val)) =
      List.ofFn (fun i => List.ofFn (c.1.2.2.2.2 (is i))) := by
  simp only [select,List.map_ofFn,ofCandidate_variables]
  congr 1
  funext i
  exact PositiveCertificateMachine.getD_ofFn _ (is i) []

def block (start count : ℕ) : List ℕ := (List.range count).map (start+·)
def parameterPlan (entries parameters : ℕ) : Plan :=
  [block 5 parameters,[],block (5+parameters) entries,block (5+parameters+entries) 3]
def localPlan (entries : ℕ) : Plan :=
  [block 5 entries,block (5+entries) entries,
    block (5+(entries+entries)) entries,block (5+(entries+entries)+entries) 3]

theorem block_parameter (m q : ℕ) : block 5 q =
    List.ofFn (fun i => (OriginalVariableLayout.parameter m q i).val) := by
  rw [block,DensePrograms.range_map]
  rfl
theorem block_original (m q : ℕ) : block (5+q) m =
    List.ofFn (fun i => (OriginalVariableLayout.original m q i).val) := by
  rw [block,DensePrograms.range_map]
  congr 1
  funext i
  simp only [OriginalVariableLayout.original,Fin.val_natAdd,Fin.val_castAdd]
  omega
theorem block_special (m q : ℕ) : block (5+q+m) 3 =
    List.ofFn (fun i => (OriginalVariableLayout.special m q i).val) := by
  rw [block,DensePrograms.range_map]
  congr 1
  funext i
  simp only [OriginalVariableLayout.special,Fin.val_natAdd]
  omega

/-- These are list semantics, not instructions for finding a complex root. -/
noncomputable def decodeList {K : Type*} [Field K] [Algebra ℚ K]
    (z : K) (v : List ℚ) : K :=
  ((List.range v.length).map (fun i => v.getD i 0 • z^i)).sum

private theorem range_map_universe {A : Type*} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  rw [List.ofFn_eq_map,
    ← Holant.Complexity.FixedGadgetSubstitution.Compiler.finRange_values,
    List.map_map]
  rfl

@[simp] theorem decodeList_ofFn {K : Type*} [Field K] [Algebra ℚ K]
    {d : ℕ} (z : K) (v : PowerArithmetic.Vector d) :
    decodeList z (List.ofFn v)=PowerArithmetic.decode z v := by
  rw [decodeList,List.length_ofFn,range_map_universe,List.sum_ofFn,
    PowerArithmetic.decode_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [PositiveCertificateMachine.getD_ofFn v i 0]

theorem decodeList_coe (z : AlgebraicComplex) (v : List ℚ) :
    ((decodeList (K:=AlgebraicComplex) z v : AlgebraicComplex) : ℂ)=
      decodeList (K:=ℂ) (z : ℂ) v := by
  simp only [decodeList,range_map_universe,List.sum_ofFn,IntermediateField.coe_sum,
    IntermediateField.coe_smul,IntermediateField.coe_pow]

noncomputable def variableValue {K : Type*} [Field K] [Algebra ℚ K]
    (z : K) (o : Output) (i : ℕ) : K := decodeList z (o.variables.getD i [])
noncomputable def matrixValue {K : Type*} [Field K] [Algebra ℚ K]
    (z : K) (o : Output) : Kernel K := fun u v => decodeList z (o.matrix.entry u v)
noncomputable def inverseValue {K : Type*} [Field K] [Algebra ℚ K]
    (z : K) (o : Output) : Kernel K := fun u v => decodeList z (o.inverse.entry u v)
noncomputable def pointValue {K τ : Type*} [Field K] [Algebra ℚ K]
    (address : τ → ℕ) (z : K) (o : Output) : SymbolicTransform.Variables τ → K :=
  Sum.elim (fun i => variableValue z o i.val) (fun p => variableValue z o (address p))

theorem variableValue_coe (z : AlgebraicComplex) (o : Output) (i : ℕ) :
    ((variableValue (K:=AlgebraicComplex) z o i : AlgebraicComplex) : ℂ)=
      variableValue (K:=ℂ) (z : ℂ) o i :=
  decodeList_coe z (o.variables.getD i [])

theorem matrixValue_coe (z : AlgebraicComplex) (o : Output) :
    (fun u v => ((matrixValue (K:=AlgebraicComplex) z o u v : AlgebraicComplex) : ℂ))=
      matrixValue (K:=ℂ) (z : ℂ) o := by
  funext u v
  exact decodeList_coe z (o.matrix.entry u v)
theorem inverseValue_coe (z : AlgebraicComplex) (o : Output) :
    (fun u v => ((inverseValue (K:=AlgebraicComplex) z o u v : AlgebraicComplex) : ℂ))=
      inverseValue (K:=ℂ) (z : ℂ) o := by
  funext u v
  exact decodeList_coe z (o.inverse.entry u v)

@[simp] theorem variable_ofCandidate {K : Type*} [Field K] [Algebra ℚ K]
    {m k : ℕ} (z : K) (c : PositiveWitnessSearch.Candidate m k) (i : Fin (5+k)) :
    variableValue z (ofCandidate c) i.val=PowerArithmetic.decode z (c.1.2.2.2.2 i) := by
  rw [variableValue,ofCandidate_variables,
    PositiveCertificateMachine.getD_ofFn (fun j => List.ofFn (c.1.2.2.2.2 j)) i [],decodeList_ofFn]
@[simp] theorem matrix_ofCandidate {K : Type*} [Field K] [Algebra ℚ K]
    {m k : ℕ} (z : K) (c : PositiveWitnessSearch.Candidate m k) (u v : Bool) :
    matrixValue z (ofCandidate c) u v=
      PowerArithmetic.decode z (MatrixWitness.matrixCode c.1.2.2.2.2 u v) := by
  rw [matrixValue,ofCandidate_matrix,decodeList_ofFn]
@[simp] theorem inverse_ofCandidate {K : Type*} [Field K] [Algebra ℚ K]
    {m k : ℕ} (z : K) (c : PositiveWitnessSearch.Candidate m k) (u v : Bool) :
    inverseValue z (ofCandidate c) u v=
      PowerArithmetic.decode z (MatrixWitness.inverseCode c.1.2.1 c.1.2.2.2.2 u v) := by
  rw [inverseValue,ofCandidate_inverse,decodeList_ofFn]

theorem matrix_function_ofCandidate {K : Type*} [Field K] [Algebra ℚ K]
    {m k : ℕ} (z : K) (c : PositiveWitnessSearch.Candidate m k) :
    matrixValue z (ofCandidate c)=fun u v =>
      PowerArithmetic.decode z (MatrixWitness.matrixCode c.1.2.2.2.2 u v) := by
  funext u v
  exact matrix_ofCandidate z c u v
theorem inverse_function_ofCandidate {K : Type*} [Field K] [Algebra ℚ K]
    {m k : ℕ} (z : K) (c : PositiveWitnessSearch.Candidate m k) :
    inverseValue z (ofCandidate c)=fun u v =>
      PowerArithmetic.decode z (MatrixWitness.inverseCode c.1.2.1 c.1.2.2.2.2 u v) := by
  funext u v
  exact inverse_ofCandidate z c u v

theorem relation_of_returned_root {m k : ℕ} (c : PositiveWitnessSearch.Candidate m k)
    (z : ℂ) (hr : (ofCandidate c).root.Represents z) :
    z^(c.1.1+1)=PowerArithmetic.decode z c.1.2.1 := by
  apply PowerArithmetic.relation_of_root
  simpa only [ofCandidate,ofStructured,StructuredWitness.emit,RootCode.polynomial,
    ComplexIsolation.Certificate.rootCode,CommonPrimitive.relationCode_polynomial] using hr.2.2.1

theorem point_matrix {K τ : Type*} [Field K] [Algebra ℚ K] {m k : ℕ}
    (address : τ → ℕ) (z : K) (c : PositiveWitnessSearch.Candidate m k) :
    SymbolicTransform.matrix (pointValue address z (ofCandidate c))=matrixValue z (ofCandidate c) := by
  funext u v
  rw [matrix_ofCandidate]
  change variableValue z (ofCandidate c) (Fin.castAdd k (MatrixWitness.index u v)).val = _
  exact variable_ofCandidate z c (Fin.castAdd k (MatrixWitness.index u v))

/-- The matrix part of a point is independent of its branch address map. -/
theorem point_inverse {K τ : Type*} [Field K] [Algebra ℚ K] {m k : ℕ}
    (address : τ → ℕ) (z : K) (c : PositiveWitnessSearch.Candidate m k)
    (hz : z^(c.1.1+1)=PowerArithmetic.decode z c.1.2.1) :
    SymbolicTransform.inverse (pointValue address z (ofCandidate c))=inverseValue z (ofCandidate c) := by
  funext u v
  rw [inverse_ofCandidate]
  unfold MatrixWitness.inverseCode
  rw [PowerArithmetic.decode_mul z c.1.2.1 _ _ hz]
  rw [SymbolicTransform.inverse,point_matrix]
  change variableValue z (ofCandidate c) 4 * _ = _
  rw [show (4 : ℕ)=(Fin.castAdd k (4 : Fin 5)).val from rfl,variable_ofCandidate]
  by_cases h : u=v
  · simp only [SymbolicTransform.adjugate,h,ite_true,matrix_ofCandidate]
  · simp only [SymbolicTransform.adjugate,h,ite_false,matrix_ofCandidate,map_neg]

variable {s : ℕ} (arity : Fin s → ℕ)

def productCoordinates (o : Output) (p : ProductBranch.Parameters arity) : List ℚ :=
  o.variables.getD (OriginalProductSystem.parameterVariable arity p).val []
def localScaleCoordinates (o : Output) (p : LocalAffineBranch.Parameters arity) : List ℚ :=
  o.variables.getD (OriginalLocalAffineSystem.scaleVariable arity p).val []
def localReciprocalCoordinates (o : Output) (p : LocalAffineBranch.Parameters arity) : List ℚ :=
  o.variables.getD (OriginalLocalAffineSystem.inverseVariable arity p).val []
def affineCoordinates (o : Output) (j : ProductVariableLayout.Slot s) : List ℚ :=
  o.variables.getD (OriginalAffineSystem.scaleVariable arity j).val []

noncomputable def productPoint (z : ℂ) (o : Output) :=
  pointValue (fun p => (OriginalProductSystem.parameterVariable arity p).val) z o
noncomputable def localPoint (z : ℂ) (o : Output) :=
  pointValue (fun p => (OriginalLocalAffineSystem.scaleVariable arity p).val) z o
noncomputable def affinePoint (z : ℂ) (o : Output) :=
  pointValue (fun j => (OriginalAffineSystem.scaleVariable arity j).val) z o

theorem productPoint_source {m : ℕ}
    (c : PositiveWitnessSearch.Candidate m (OriginalProductSystem.Extra arity)) (z : ℂ) :
    productPoint arity z (ofCandidate c)=OriginalProductSystem.point arity
      (fun i => PowerArithmetic.decode z (c.1.2.2.2.2 i)) := by
  funext p
  cases p with
  | inl i =>
      change variableValue z (ofCandidate c)
        (OriginalVariableLayout.matrix (OriginalProductSystem.Entries arity) (OriginalProductSystem.Count arity) i).val =
          PowerArithmetic.decode z (c.1.2.2.2.2
            (OriginalVariableLayout.matrix (OriginalProductSystem.Entries arity) (OriginalProductSystem.Count arity) i))
      exact variable_ofCandidate z c
        (OriginalVariableLayout.matrix (OriginalProductSystem.Entries arity) (OriginalProductSystem.Count arity) i)
  | inr p =>
      change variableValue z (ofCandidate c) (OriginalProductSystem.parameterVariable arity p).val =
        PowerArithmetic.decode z (c.1.2.2.2.2 (OriginalProductSystem.parameterVariable arity p))
      exact variable_ofCandidate z c (OriginalProductSystem.parameterVariable arity p)

theorem localPoint_source {m : ℕ}
    (c : PositiveWitnessSearch.Candidate m (OriginalLocalAffineSystem.Extra arity)) (z : ℂ) :
    localPoint arity z (ofCandidate c)=OriginalLocalAffineSystem.point arity
      (fun i => PowerArithmetic.decode z (c.1.2.2.2.2 i)) := by
  funext p
  cases p with
  | inl i =>
      change variableValue z (ofCandidate c)
        (OriginalVariableLayout.matrix (OriginalLocalAffineSystem.Entries arity) (OriginalLocalAffineSystem.Count arity) i).val =
          PowerArithmetic.decode z (c.1.2.2.2.2
            (OriginalVariableLayout.matrix (OriginalLocalAffineSystem.Entries arity) (OriginalLocalAffineSystem.Count arity) i))
      exact variable_ofCandidate z c
        (OriginalVariableLayout.matrix (OriginalLocalAffineSystem.Entries arity) (OriginalLocalAffineSystem.Count arity) i)
  | inr p =>
      change variableValue z (ofCandidate c) (OriginalLocalAffineSystem.scaleVariable arity p).val =
        PowerArithmetic.decode z (c.1.2.2.2.2 (OriginalLocalAffineSystem.scaleVariable arity p))
      exact variable_ofCandidate z c (OriginalLocalAffineSystem.scaleVariable arity p)

theorem affinePoint_source {m : ℕ}
    (c : PositiveWitnessSearch.Candidate m (OriginalAffineSystem.Extra arity)) (z : ℂ) :
    affinePoint arity z (ofCandidate c)=OriginalAffineSystem.point arity
      (fun i => PowerArithmetic.decode z (c.1.2.2.2.2 i)) := by
  funext p
  cases p with
  | inl i =>
      change variableValue z (ofCandidate c)
        (OriginalVariableLayout.matrix (OriginalAffineSystem.Entries arity) (s+1) i).val =
          PowerArithmetic.decode z (c.1.2.2.2.2
            (OriginalVariableLayout.matrix (OriginalAffineSystem.Entries arity) (s+1) i))
      exact variable_ofCandidate z c
        (OriginalVariableLayout.matrix (OriginalAffineSystem.Entries arity) (s+1) i)
  | inr j =>
      change variableValue z (ofCandidate c) (OriginalAffineSystem.scaleVariable arity j).val =
        PowerArithmetic.decode z (c.1.2.2.2.2 (OriginalAffineSystem.scaleVariable arity j))
      exact variable_ofCandidate z c (OriginalAffineSystem.scaleVariable arity j)

end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers
