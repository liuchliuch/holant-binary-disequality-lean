import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemMachine
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Original
import Holant.Proofs.Tractability.AffineMachine.AccessPrograms

/-!
# Uniform polynomial tests of original algebraic RootCodes

The programme is fixed by a rational-expression system and the number of bound
and existential coordinates. Runtime input is ONLY the original RootCode list;
values, a coefficient field, transforms, a correct evaluator, solution witnesses,
and successful search heights are not inputs. The existing two-sided algebraic
search decides both answers. A companion programme emits the existing actual
encoded algebraic witness, without rerunning a separate semantic selection.

This component supports prescribed K arithmetic by adjoining the already known
literal i and positive sqrt(2) RootCodes as input constants. It avoids selecting
a field/presentation from the values under recognition. It is a uniform exact
polynomial-system decision component, not yet the full seven-criterion compiler.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.PolynomialDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Finite syntax; no embedded field values or evaluation callbacks. -/
inductive Expr (n : ℕ) where
  | constant (value : ℚ)
  | variable (index : Fin n)
  | add (left right : Expr n)
  | mul (left right : Expr n)
  | neg (value : Expr n)

namespace Expr
variable {n : ℕ}
def eval {E : Type} [Field E] [Algebra ℚ E] (x : Fin n → E) : Expr n → E
  | .constant c => algebraMap ℚ E c
  | .variable i => x i
  | .add a b => eval x a + eval x b
  | .mul a b => eval x a * eval x b
  | .neg a => -eval x a

def rename {k : ℕ} (f : Fin n → Fin k) : Expr n → Expr k
  | .constant c => .constant c
  | .variable i => .variable (f i)
  | .add a b => .add (rename f a) (rename f b)
  | .mul a b => .mul (rename f a) (rename f b)
  | .neg a => .neg (rename f a)

theorem eval_rename {k : ℕ} {E : Type} [Field E] [Algebra ℚ E]
    (f : Fin n → Fin k) (x : Fin k → E) (e : Expr n) :
    (rename f e).eval x=e.eval (fun i => x (f i)) := by
  induction e <;> simp_all [rename,eval]

def sum (es : List (Expr n)) : Expr n := es.foldr .add (.constant 0)
def product (es : List (Expr n)) : Expr n := es.foldr .mul (.constant 1)
def power (e : Expr n) (k : ℕ) : Expr n := product (List.replicate k e)

theorem eval_sum {E : Type} [Field E] [Algebra ℚ E]
    (x : Fin n → E) (es : List (Expr n)) : (sum es).eval x=(es.map (eval x)).sum := by
  induction es with
  | nil => simp [sum,eval]
  | cons e es ih => simpa only [sum,List.foldr_cons,eval,List.map_cons,List.sum_cons] using congrArg (fun z => eval x e+z) ih

theorem eval_product {E : Type} [Field E] [Algebra ℚ E]
    (x : Fin n → E) (es : List (Expr n)) : (product es).eval x=(es.map (eval x)).prod := by
  induction es with
  | nil => simp [product,eval]
  | cons e es ih => simpa only [product,List.foldr_cons,eval,List.map_cons,List.prod_cons] using congrArg (fun z => eval x e*z) ih

theorem eval_power {E : Type} [Field E] [Algebra ℚ E]
    (x : Fin n → E) (e : Expr n) (k : ℕ) : (power e k).eval x=(eval x e)^k := by
  simp [power,eval_product]

theorem map_eval {E E' : Type} [Field E] [Algebra ℚ E] [Field E'] [Algebra ℚ E']
    (φ : E →ₐ[ℚ] E') (x : Fin n → E) (e : Expr n) :
    φ (e.eval x)=e.eval (fun i => φ (x i)) := by
  induction e with
  | constant c => exact φ.commutes c
  | «variable» i => rfl
  | add a b ha hb => simp only [eval,map_add,ha,hb]
  | mul a b ha hb => simp only [eval,map_mul,ha,hb]
  | neg a ha => simp only [eval,map_neg,ha]

/-- Original/free values occupy the suffix; five independent guard coordinates
precede them. The matrix guard is internally discharged by literal identity. -/
def compile : Expr n → Sparse.Poly (5+n) 1
  | .constant c => SparseTransform.constant (fun _ => c)
  | .variable i => SparseTransform.variableCode RationalCompiler.data (Fin.natAdd 5 i)
  | .add a b => Sparse.add a.compile b.compile
  | .mul a b => Sparse.mul RationalCompiler.data a.compile b.compile
  | .neg a => Sparse.neg a.compile

theorem compile_eval (x : Fin (5+n) → ℂ) (e : Expr n) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) x e.compile=
      e.eval (fun i => x (Fin.natAdd 5 i)) := by
  induction e with
  | constant c => simp [compile,eval,RationalCompiler.decode_eq]
  | «variable» i =>
    change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) x
      (SparseTransform.variableCode RationalCompiler.field.toArithmeticData (Fin.natAdd 5 i))=_
    exact SparseEvaluation.variable_eval _ _ _ _
  | add a b ha hb => simp [compile,eval,ha,hb]
  | mul a b ha hb =>
    change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) x
      (Sparse.mul RationalCompiler.field.toArithmeticData a.compile b.compile)=_
    rw [SparseEvaluation.mul_eval,ha,hb]
    rfl
  | neg a ha => simp [compile,eval,ha]
end Expr

variable {m q : ℕ}

def body (es : List (Expr (m+q))) : List (Sparse.Poly (5+(m+q)) 1) :=
  SparseTransform.guard RationalCompiler.data (m+q) :: es.map Expr.compile

def address (i : Fin m) : Fin (5+(m+q)) := Fin.natAdd 5 (Fin.castAdd q i)
def identityPoint : Fin 5 → ℂ := ![1,0,0,1,1]
def fill (w : Fin m → ℂ) (u : Fin q → ℂ) : Fin (5+(m+q)) → ℂ :=
  Fin.addCases identityPoint (Fin.addCases w u)

@[simp] theorem fill_address (w : Fin m → ℂ) (u : Fin q → ℂ) (i : Fin m) :
    fill w u (address i)=w i := by simp [fill,address]
@[simp] theorem fill_tail (w : Fin m → ℂ) (u : Fin q → ℂ) (i : Fin (m+q)) :
    fill w u (Fin.natAdd 5 i)=Fin.addCases w u i := by simp [fill]

theorem fill_guard (w : Fin m → ℂ) (u : Fin q → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ)
      (fill w u) (SparseTransform.guard RationalCompiler.data (m+q))=0 := by
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill w u)
    (SparseTransform.guard RationalCompiler.field.toArithmeticData (m+q))=0
  rw [SparseEvaluation.guard_eval]
  simp [fill,identityPoint,SymbolicTransform.determinant,SymbolicTransform.matrix,
    SymbolicTransform.index,SparseTransform.point]

/-- Exact existential semantics, with all original conjugates bound separately. -/
theorem solutions_iff (w : Fin m → ℂ) (es : List (Expr (m+q))) :
    (∃ x : Fin (5+(m+q)) → ℂ,
      (∀ i, x (address i)=w i) ∧
      ∀ p ∈ body es, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) x p=0) ↔
    ∃ u : Fin q → ℂ, ∀ e ∈ es, e.eval (Fin.addCases w u)=0 := by
  constructor
  · rintro ⟨x,hx,he⟩
    let u : Fin q → ℂ := fun j => x (Fin.natAdd 5 (Fin.natAdd m j))
    have ht : (fun i : Fin (m+q) => x (Fin.natAdd 5 i))=Fin.addCases w u := by
      funext i
      induction i using Fin.addCases with
      | left i => simpa only [Fin.addCases_left,address] using hx i
      | right i => simp only [Fin.addCases_right]; rfl
    refine ⟨u,?_⟩
    intro e hem
    have h := he e.compile (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e,hem,rfl⟩))
    rw [Expr.compile_eval,ht] at h
    exact h
  · rintro ⟨u,hu⟩
    refine ⟨fill w u,fill_address w u,?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact fill_guard w u
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
      rw [Expr.compile_eval]
      simpa only [fill_tail] using hu e he

abbrev inputEncoding := framedListEncoding ComplexIsolation.CertificateMachine.rootEncoding

def request (es : List (Expr (m+q))) (roots : List RootCode) : RationalInputMachine.Input :=
  ⟨5+(m+q),roots,RationalInputMachine.bodyWire (body es),
    List.ofFn (fun i : Fin m => (address (q:=q) i).val)⟩

def requestComputes (es : List (Expr (m+q))) :
    Computes inputEncoding RationalInputMachine.encoding (request es) := by
  let size := constantComputes inputEncoding encodingNatBool (5+(m+q))
  let rows := constantComputes inputEncoding RationalInputMachine.bodyEncoding
    (RationalInputMachine.bodyWire (body es))
  let addresses := constantComputes inputEncoding RationalInputMachine.addressesEncoding
    (List.ofFn (fun i : Fin m => (address (q:=q) i).val))
  exact recode (pairComputes size
    (pairComputes (identityComputes inputEncoding) (pairComputes rows addresses)))
    id (fun _ => rfl) (fun _ => rfl)

theorem request_exact (input : Fin m → RootCode) (es : List (Expr (m+q))) :
    request es (List.ofFn input)=RationalInputMachine.fromSource input (body es) address := rfl

/-- One machine for all legal input coefficient values at the fixed arities. -/
def machine (es : List (Expr (m+q))) : BinaryCompose.Machine :=
  (requestComputes es).machine.compose OriginalSystemMachine.machine

def answer (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (es : List (Expr (m+q))) : Bool :=
  OriginalSystemDecision.answer input hv (body es) address

theorem source_outputs (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (es : List (Expr (m+q))) : ∃ ticks, Nonempty (TM2OutputsInTime (machine es).computer
      (inputEncoding.encode (List.ofFn input))
      (some (encodingBoolBool.encode (answer input hv es))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := OriginalSystemMachine.source_outputs input hv (body es) address
  have left := (requestComputes es).outputs (List.ofFn input)
  rw [request_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem answer_correct (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (input i).Represents (w i : ℂ))
    (es : List (Expr (m+q))) :
    answer input hv es=true ↔
      ∃ u : Fin q → ℂ, ∀ e ∈ es, e.eval (Fin.addCases (fun i => (w i : ℂ)) u)=0 := by
  rw [answer,OriginalSystemDecision.answer_correct input hv w hw (body es) address
    (List.mem_cons_self ..)]
  simp_rw [RationalInputSystem.system_zero_iff]
  exact solutions_iff _ es

theorem answer_false_iff (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (input i).Represents (w i : ℂ))
    (es : List (Expr (m+q))) :
    answer input hv es=false ↔
      ¬∃ u : Fin q → ℂ, ∀ e ∈ es, e.eval (Fin.addCases (fun i => (w i : ℂ)) u)=0 := by
  have hb : ∀ b : Bool, b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,answer_correct input hv w hw es]

/-- Ground arithmetic tests are genuine two-sided decisions of the represented
original values; no algebraic coordinates or semantic equality decider is input. -/
theorem ground_correct (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (input i).Represents (w i : ℂ))
    (e : Expr m) : answer (q:=0) input hv [e]=true ↔ e.eval (fun i => (w i : ℂ))=0 := by
  rw [answer_correct (q:=0) input hv w hw [e]]
  have args (u : Fin 0 → ℂ) :
      (Fin.addCases (fun i : Fin m => (w i : ℂ)) u : Fin (m+0) → ℂ)=(fun i => (w i : ℂ)) := by
    funext i
    exact Fin.addCases_left (m:=m) (n:=0) (motive:=fun _ => ℂ) (left:=fun i : Fin m => (w i : ℂ)) (right:=u) i
  simp only [args,List.mem_singleton,forall_eq]
  constructor
  · rintro ⟨_,h⟩; exact h
  · intro h; exact ⟨Fin.elim0,h⟩

/-- The companion emits the old complete algebraic witness wire, not just a
positive Boolean. Its search and literal original bindings are unchanged. -/
def witnessMachine (es : List (Expr (m+q))) : BinaryCompose.Machine :=
  (requestComputes es).machine.compose WitnessOutput.originalMachine

def witness (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (es : List (Expr (m+q))) : Option WitnessOutput.Output :=
  WitnessOutput.originalOutput input hv (body es) address

theorem witness_outputs (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (es : List (Expr (m+q))) : ∃ ticks, Nonempty (TM2OutputsInTime (witnessMachine es).computer
      (inputEncoding.encode (List.ofFn input))
      (some (WitnessOutput.resultEncoding.encode (witness input hv es))) ticks) := by
  obtain ⟨ticks,⟨right⟩⟩ := WitnessOutput.original_outputs input hv (body es) address
  have left := (requestComputes es).outputs (List.ofFn input)
  rw [request_exact] at left
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ left right⟩⟩

theorem witness_isSome_iff (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (input i).Represents (w i : ℂ))
    (es : List (Expr (m+q))) :
    (witness input hv es).isSome=true ↔
      ∃ u : Fin q → ℂ, ∀ e ∈ es, e.eval (Fin.addCases (fun i => (w i : ℂ)) u)=0 :=
  (WitnessOutput.originalOutput_isSome input hv (body es) address).trans
    (answer_correct input hv w hw es)

/-- Same-machine elementary work and every-prefix storage, with the bound
produced from the actual unbounded algebraic search receipt. -/
theorem source_resources (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (es : List (Expr (m+q))) : ∃ ticks, ∃ out : TM2OutputsInTime (machine es).computer
      (inputEncoding.encode (List.ofFn input))
      (some (encodingBoolBool.encode (answer input hv es))) ticks,
    primitiveCost (machine es) out.steps
      (some (initList (machine es).computer (inputEncoding.encode (List.ofFn input))))≤
        ticks*(machine es).primitiveBudget ∧
    ∀ j≤out.steps, ∀ cfg : (machine es).Config,
      (fun p => p.bind (machine es).computer.step)^[j]
        (some (initList (machine es).computer (inputEncoding.encode (List.ofFn input))))=some cfg →
      stackSize cfg.stk≤(inputEncoding.encode (List.ofFn input)).length+
        ticks*(machine es).primitiveBudget := by
  obtain ⟨ticks,⟨out⟩⟩ := source_outputs input hv es
  refine ⟨ticks,out,(primitiveCost_le _ _ _).trans
    (Nat.mul_le_mul_right _ out.steps_le_m),?_⟩
  intro j hj cfg hcfg
  have hs := (machine es).run_size_le _ cfg j hcfg
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hj.trans out.steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.PolynomialDecision
