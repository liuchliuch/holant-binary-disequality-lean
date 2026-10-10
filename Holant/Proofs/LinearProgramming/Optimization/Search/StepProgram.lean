import Holant.Proofs.LinearProgramming.Complexity.ListLemmas
import Holant.Proofs.LinearProgramming.Optimization.Search.UpdateProgram
import Holant.Proofs.LinearProgramming.Optimization.Search.ScannerPolynomial

/-!
One actual original-input search round: first violated constraint scan,
normal emission, literal zero-word test, physical update and physical storage.
No normal or valid separator is supplied by the caller. The output retains
the same original Input. Eager candidate computation is included even on
terminal branches. Whole-loop preparation, counter and final output remain
separate from this proved polynomial physical round.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity


namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.StepProgram
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open FactorUpdate Codec CutProgram StackProtocol
noncomputable section

abbrev Query := StorageProgram.Query
def encoding := StorageProgram.queryEncoding
def tags (q : Query) : List Tag := Scanner.value (q.1,q.2.1)
def normal (q : Query) : List ℚ := (CutProgram.value (q.1,(tags q).getD 0 (false,0,false))).1
def candidate (q : Query) : Query :=
  (q.1,StorageProgram.value (q.1,UpdateProgram.value (q.1,q.2,normal q)))
def value (q : Query) : Query :=
  if tags q=[] then q else if normal q=List.replicate q.1.val.dimension 0 then q else candidate q

def source := StorageProgram.source
def state := StorageProgram.stored
def center := state.andThen (Wiring.firstComputes pointEncoding StorageProgram.matrixEncoding)
def scannerComputes : Computes encoding Scanner.answerEncoding tags :=
  (pairComputes source center).andThen ScannerPolynomial.computes
def normalComputes : Computes encoding pointEncoding normal := by
  let chosen := AccessPrograms.get tagEncoding (false,0,false) scannerComputes
    (constantComputes encoding UnaryBinary.unaryEncoding 0)
  exact ((pairComputes source chosen).andThen CutProgram.computes).andThen
    (Wiring.firstComputes pointEncoding rationalEncoding)
def zeroComputes : Computes encoding pointEncoding (fun q : Query => List.replicate q.1.val.dimension (0 : ℚ)) :=
  (source.andThen BudgetProgram.dimension).andThen (WireLists.replicate rationalEncoding 0)
def candidateComputes : Computes encoding encoding candidate := by
  let update := (pairComputes source (pairComputes state normalComputes)).andThen UpdateProgram.computes
  let stored := (pairComputes source update).andThen StorageProgram.computes
  exact pairComputes source stored
def computes : Computes encoding encoding value := by
  let empty := (pairComputes scannerComputes (constantComputes encoding Scanner.answerEncoding [])).andThen
    (equalComputes Scanner.answerEncoding)
  let zero := (pairComputes normalComputes zeroComputes).andThen (equalComputes pointEncoding)
  exact congrComputes (ifComputes empty (identityComputes encoding)
    (ifComputes zero (identityComputes encoding) candidateComputes)) (fun q => by simp [value])


theorem ofFn_zero {n : ℕ} (v : Vec n) : List.ofFn v=List.replicate n 0 ↔ v=0 := by
  constructor
  · intro h
    funext i
    have he := congrArg (fun xs => xs.getD i.val 0) h
    rw [DensePrograms.getD_ofFn,List.getD_replicate (0 : ℚ) i.isLt] at he
    exact he
  · intro h
    subst v
    exact List.ofFn_const n (0 : ℚ)

private theorem decoded_center {n : ℕ} (s : FactorUpdate.State n) :
    (fun j : Fin n => (List.ofFn s.center).getD j.val 0)=s.center :=
  funext (fun j => DensePrograms.getD_ofFn s.center j 0)

theorem scanner_exact (d : Input) (s : FactorUpdate.State d.val.dimension) :
    tags (d,StorageProgram.code s)=
      (Separation.separate d.val s.center).toList.map (constraintTag d.val) := by
  change Scanner.value (d,List.ofFn s.center)=_
  rw [Scanner.value_exact,decoded_center]

theorem normal_exact (d : Input) (s : FactorUpdate.State d.val.dimension) (c : Separation.Constraint d.val)
    (hc : Separation.separate d.val s.center=some c) :
    normal (d,StorageProgram.code s)=List.ofFn (Separation.normal d.val c) := by
  have ht := scanner_exact d s
  rw [hc] at ht
  change tags (d,StorageProgram.code s)=[constraintTag d.val c] at ht
  unfold normal
  rw [ht]
  change (CutProgram.value (d,constraintTag d.val c)).1=List.ofFn (Separation.normal d.val c)
  exact congrArg Prod.fst (CutProgram.correct d c)

theorem normal_at (d : Input) (s : FactorUpdate.State d.val.dimension) (c : Separation.Constraint d.val)
    (hc : Separation.separate d.val s.center=some c) (j : Fin d.val.dimension) :
    (normal (d,StorageProgram.code s)).getD j.val 0=Separation.normal d.val c j := by
  rw [normal_exact d s c hc]
  exact DensePrograms.getD_ofFn _ j 0

theorem source_preserved (q : Query) : (value q).1=q.1 := by
  unfold value
  split_ifs <;> rfl

theorem original_raw_preserved (q : Query) : (value q).1.val=q.1.val :=
  congrArg Subtype.val (source_preserved q)

private theorem accepted_preserves (d : Input) (s : FactorUpdate.State d.val.dimension)
    (hc : Separation.separate d.val s.center=none) :
    value (d,StorageProgram.code s)=(d,StorageProgram.code s) := by
  have ht : tags (d,StorageProgram.code s)=[] := by
    rw [scanner_exact,hc]
    rfl
  rw [value,if_pos ht]

private theorem candidate_code (d : Input) (hn : 2≤d.val.dimension)
    (s : FactorUpdate.State d.val.dimension) (c : Separation.Constraint d.val)
    (hR : s.factor.det≠0) (hc : Separation.separate d.val s.center=some c)
    (hg : Separation.normal d.val c≠0) :
    candidate (d,StorageProgram.code s)=
      (d,StorageProgram.code (RoundedGeometry.value (FactorUpdate.update s (Separation.normal d.val c))
        (GridPrecision.grid d.val) (RoundingDeterminant.eta d.val.dimension))) := by
  change (d,StorageProgram.value (d,UpdateProgram.value
    (d,StorageProgram.code s,normal (d,StorageProgram.code s))))=_
  rw [normal_exact d s c hc,UpdateProgram.correct d hn s _ hR hg,StorageProgram.correct]

/-- Both branches are outputs of actual programs. On active rounds only
nonsingularity is needed; valid-cut correctness is derived by Separation and
RoundedTrajectory, not a premise of this physical semantic identification.
-/
theorem correct (d : Input) (hn : 2≤d.val.dimension) (s : FactorUpdate.State d.val.dimension) (hR : s.factor.det≠0) :
    value (d,StorageProgram.code s)=(d,StorageProgram.code (RoundedTrajectory.step d.val s)) := by
  cases hc : Separation.separate d.val s.center with
  | none =>
    rw [accepted_preserves d s hc]
    simp only [RoundedTrajectory.step,hc]
  | some c =>
    have hs : tags (d,StorageProgram.code s)≠[] := by simp [scanner_exact,hc]
    have hnword := normal_exact d s c hc
    rw [value,if_neg hs,hnword]
    by_cases hg : Separation.normal d.val c=0
    · rw [if_pos ((ofFn_zero _).mpr hg)]
      simp only [RoundedTrajectory.step,hc,if_pos hg]
    · rw [if_neg (fun h => hg ((ofFn_zero _).mp h))]
      simpa only [RoundedTrajectory.step,hc,if_neg hg] using candidate_code d hn s c hR hc hg

theorem actual_round (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k<GridPrecision.iterations d.val) :
    value (d,StorageProgram.code (RoundedTrajectory.run d.val k))=
      (d,StorageProgram.code (RoundedTrajectory.run d.val (k+1))) := by
  rw [correct d hn _ (RoundedTrajectory.invariant d.val hn k hk.le).1]
  exact congrArg (fun s => (d,StorageProgram.code s)) (RoundedTrajectory.run_succ d.val k).symm

theorem inFP : InFP encoding encoding value := computes.inFP
theorem execution (q : Query) :
    RunsExactly computes.machine.computer.step
      (initList computes.machine.computer (encoding.encode q))
      (haltList computes.machine.computer (encoding.encode (value q)))
      (computes.outputs q).steps := (computes.outputs q).evals_in_steps

private theorem computes_encoded_execution {A B : Type}
    {ea : Encoding A Bool} {eb : Encoding B Bool} {f : A → B}
    (M : Computes ea eb f) (a : A) (b : B) (he : f a = b) :
    (fun c : Option M.machine.Config => c.bind M.machine.computer.step)^[
      (M.outputs a).steps]
      (some (initList M.machine.computer (ea.encode a))) =
        some (haltList M.machine.computer (eb.encode b)) := by
  subst b
  exact (M.outputs a).evals_in_steps

/-- This run is the actual eager physical round, not the mathematical
iteration promoted to a machine. Its invariant comes from the old trajectory. -/
theorem actual_execution (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k<GridPrecision.iterations d.val) :
    RunsExactly computes.machine.computer.step
      (initList computes.machine.computer
        (encoding.encode (d,StorageProgram.code (RoundedTrajectory.run d.val k))))
      (haltList computes.machine.computer
        (encoding.encode (d,StorageProgram.code (RoundedTrajectory.run d.val (k+1)))))
      (computes.outputs (d,StorageProgram.code (RoundedTrajectory.run d.val k))).steps := by
  exact computes_encoded_execution computes
    (d,StorageProgram.code (RoundedTrajectory.run d.val k))
    (d,StorageProgram.code (RoundedTrajectory.run d.val (k+1)))
    (actual_round d hn k hk)

def queryPolynomial : Polynomial ℕ := 2*Polynomial.X+1+StorageProgram.statePolynomial
def roundPolynomial : Polynomial ℕ := computes.time.comp queryPolynomial
def temporaryPolynomial : Polynomial ℕ := queryPolynomial+
  roundPolynomial*Polynomial.C computes.machine.primitiveBudget

private theorem query_word_length (d : Input) (s : StorageProgram.Code) :
    (encoding.encode (d,s)).length=
      2*(inputEncoding.encode d).length+1+(StorageProgram.encoding.encode s).length := by
  simp only [encoding,StorageProgram.queryEncoding,pairEncoding_length]

private theorem queryPolynomial_eval (L : ℕ) : queryPolynomial.eval L=2*L+1+StorageProgram.statePolynomial.eval L := by
  simp only [queryPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat]

theorem actual_query_length (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d.val) :
    (encoding.encode (d,StorageProgram.code (RoundedTrajectory.run d.val k))).length≤
      queryPolynomial.eval (inputEncoding.encode d).length := by
  have hs := StorageProgram.actual_state_length d hn k hk
  rw [query_word_length,queryPolynomial_eval]
  omega

theorem actual_return_length (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k<GridPrecision.iterations d.val) :
    (encoding.encode (value (d,StorageProgram.code (RoundedTrajectory.run d.val k)))).length≤
      queryPolynomial.eval (inputEncoding.encode d).length := by
  rw [actual_round d hn k hk]
  exact actual_query_length d hn (k+1) (by omega)

private theorem computes_original_bound {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Computes ea eb f) (a : A) (Q : Polynomial ℕ) (L : ℕ)
    (hi : (ea.encode a).length≤Q.eval L) :
    (w.outputs a).steps≤(w.time.comp Q).eval L := by
  apply (w.outputs a).steps_le_m.trans
  rw [Polynomial.eval_comp]
  exact natPolynomial_eval_mono w.time hi

/-- A polynomial bound in ORIGINAL input bytes for the SAME physical round,
including terminal states and eager candidate arithmetic. No current-word
bound is left for the caller to certify. -/
theorem actual_steps (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d.val) :
    (computes.outputs (d,StorageProgram.code (RoundedTrajectory.run d.val k))).steps≤
      roundPolynomial.eval (inputEncoding.encode d).length := by
  exact computes_original_bound computes (d,StorageProgram.code (RoundedTrajectory.run d.val k))
    queryPolynomial (inputEncoding.encode d).length (actual_query_length d hn k hk)

theorem actual_primitive_cost (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d.val) :
    primitiveCost computes.machine
      (computes.outputs (d,StorageProgram.code (RoundedTrajectory.run d.val k))).steps
      (some (Turing.initList computes.machine.computer
        (encoding.encode (d,StorageProgram.code (RoundedTrajectory.run d.val k)))))≤
      (roundPolynomial*Polynomial.C computes.machine.primitiveBudget).eval (inputEncoding.encode d).length := by
  exact (primitiveCost_le _ _ _).trans (by
    simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_right computes.machine.primitiveBudget (actual_steps d hn k hk))

theorem actual_temporary_bits (d : Input) (hn : 2≤d.val.dimension) (k : ℕ)
    (hk : k≤GridPrecision.iterations d.val) (t : ℕ)
    (ht : t≤(computes.outputs (d,StorageProgram.code (RoundedTrajectory.run d.val k))).steps)
    (c : computes.machine.Config)
    (hc : (fun p => p.bind computes.machine.computer.step)^[t]
      (some (Turing.initList computes.machine.computer
        (encoding.encode (d,StorageProgram.code (RoundedTrajectory.run d.val k)))))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (inputEncoding.encode d).length := by
  have hs := computes.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hi := actual_query_length d hn k hk
  have hr := ht.trans (actual_steps d hn k hk)
  apply hs.trans
  simpa only [temporaryPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.add_le_add hi (Nat.mul_le_mul_right computes.machine.primitiveBudget hr)

theorem physical_cost (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (encoding.encode q)))≤
      (primitivePolynomial computes).eval (encoding.encode q).length := computes_primitive_cost computes q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.StepProgram
