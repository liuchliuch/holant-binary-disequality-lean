import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Queries
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Compile
import Holant.Proofs.BinaryInterpolation.PostprocessBounds
import Holant.Complexity.BinaryInterpolation.DivisionStack


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Postprocess
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open WeightCompiler RingFormula
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section

def coeff : Fin 4 → ℚ := WeightFormulas.coefficients 1 1
def denominator (n : ℕ) (i : Fin (n+1)) : ℚ := interpolationDenominator (nodes n) i
def numerator (n : ℕ) (i : Fin (n+1)) : ℚ := ∏ j ∈ Finset.univ.erase i,-((j.val+1 : ℕ) : ℚ)
def numeratorFormula (n : ℕ) (i : Fin (n+1)) : WeightFormulas.Formula :=
  without (fun j => .mul (.literal 2) (WeightFormulas.node false (j.val+1))) i
def weightFormula (n : ℕ) (i : Fin (n+1)) : WeightFormulas.Formula :=
  .mul (WeightFormulas.weight false n i) (numeratorFormula n i)
def totalFormula (n : ℕ) := WeightFormulas.totalDenominator false n

theorem denominator_ne_zero (n : ℕ) (i : Fin (n+1)) : denominator n i≠0 :=
  interpolationDenominator_ne_zero _ (nodes_injective n) i
theorem eval_denominator (n : ℕ) (i : Fin (n+1)) :
    (WeightFormulas.denominator false n i).eval coeff=denominator n i := by
  change (WeightFormulas.denominator false n i).eval (WeightFormulas.coefficients (1 : ℚ) 1) = _
  rw [WeightFormulas.eval_denominator]
  simp only [queryDenominator,WeightFormulas.scales,one_pow,one_mul,denominator,interpolationDenominator]
  apply Finset.prod_congr rfl
  intro j _
  simp only [WeightFormulas.nodes,nodes,Bool.false_eq_true,if_false,Nat.cast_add,Nat.cast_one]
  ring
theorem eval_numerator (n : ℕ) (i : Fin (n+1)) : (numeratorFormula n i).eval coeff=numerator n i := by
  simp only [numeratorFormula,RingFormula.eval_without,numerator]
  apply Finset.prod_congr rfl
  intro j _
  change (-1 : ℚ) * (WeightFormulas.node false (j.val+1)).eval (WeightFormulas.coefficients 1 1) = _
  rw [WeightFormulas.eval_node]
  simp
theorem eval_weight (n : ℕ) (i : Fin (n+1)) :
    (weightFormula n i).eval coeff=(∏ j ∈ Finset.univ.erase i,denominator n j)*numerator n i := by
  simp only [weightFormula,RingFormula.eval,eval_numerator,WeightFormulas.weight,RingFormula.eval_without]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact eval_denominator n j
theorem eval_total (n : ℕ) : (totalFormula n).eval coeff=BinaryInterpolation.commonDenominator (denominator n) := by
  simp only [totalFormula,WeightFormulas.totalDenominator,RingFormula.eval_prodList,
    List.map_ofFn,Fin.prod_ofFn,Function.comp_apply,eval_denominator,BinaryInterpolation.commonDenominator]

theorem lagrange_weight (n : ℕ) (i : Fin (n+1)) :
    WeightedMatchingInterpolation.weight n i=numerator n i/denominator n i := by
  have hn (j : Fin (n+1)) : (-1 : ℚ)-nodes n j=-((j.val+1 : ℕ) : ℚ) := by
    simp only [nodes,Nat.cast_add,Nat.cast_one]
    ring
  simp only [WeightedMatchingInterpolation.weight,Lagrange.basis,Polynomial.eval_prod,
    Lagrange.basisDivisor,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X]
  simp_rw [hn]
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  simp only [numerator,denominator,interpolationDenominator,div_eq_mul_inv,mul_comm]

def reference (n : ℕ) : Code (Fin 4) :=
  [.zero]++WeightedStack.code (List.ofFn (weightFormula n))++(totalFormula n).code++[.swap]
def resultPair (n : ℕ) (y : Fin (n+1) → ℚ) : ℚ × ℚ :=
  (commonNumerator (denominator n) (fun i => y i*numerator n i),BinaryInterpolation.commonDenominator (denominator n))
def trace (n : ℕ) (y : Fin (n+1) → ℚ) : List ℚ :=
  WeightedStack.trace coeff (List.ofFn (fun i => (weightFormula n i,y i))) 0++(totalFormula n).trace coeff

theorem reference_run (n : ℕ) (y : Fin (n+1) → ℚ) :
    run coeff (reference n) (List.ofFn y)=some ([(resultPair n y).1,(resultPair n y).2],trace n y) := by
  have hw := WeightedStack.run_code coeff (List.ofFn (fun i => (weightFormula n i,y i))) 0 []
  have hv : WeightedStack.value coeff (List.ofFn (fun i => (weightFormula n i,y i))) 0=(resultPair n y).1 := by
    rw [WeightedStack.value_eq_sum]
    simp only [zero_add,List.map_ofFn,Fin.sum_ofFn,Function.comp_apply,eval_weight,resultPair,commonNumerator]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [List.map_ofFn,Function.comp_def,List.append_nil] at hw
  rw [hv] at hw
  simp only [reference,run_append,run,step,bind,Option.bind_some,pure,List.nil_append]
  simp only [hw,Option.bind_some,RingFormula.run_code,eval_total]
  simp [run,step,resultPair,trace,List.append_assoc]

theorem result_value (n : ℕ) (y : Fin (n+1) → ℚ) :
    (resultPair n y).1/(resultPair n y).2=recover n (List.ofFn y) := by
  rw [resultPair,← sum_div_common _ _ (denominator_ne_zero n)]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn,lagrange_weight]
  ring

def numeratorCode (n i : ℕ) : Code (Fin 4) :=
  [.one]++(List.range (n+1)).reverse.flatMap (fun j =>
    (if j=i then [.one] else WeightCompiler.nodeCode false (j+1)++[.literal 2,.mul])++[.mul])
def weightedCode (n i : ℕ) : Code (Fin 4) :=
  numeratorCode n i++weightCode false n i++[.mul]
def generatedCode (n : ℕ) : Code (Fin 4) :=
  [.zero]++(List.range (n+1)).flatMap (fun i => weightedCode n i++[.copy 2,.mul,.add,.erase 1])++
    totalDenominatorCode false n++[.swap]

theorem numerator_code (n : ℕ) (i : Fin (n+1)) : (numeratorFormula n i).code=numeratorCode n i.val := by
  simp only [numeratorFormula,without,prodList_code]
  rw [ofFn_code_flatMap (f := fun j =>
    if j=i.val then [.one] else WeightCompiler.nodeCode false (j+1)++[.literal 2,.mul])]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j; simp [RingFormula.code]
    · have hv : j.val≠i.val := fun he => h (Fin.ext he)
      simp [h,hv,RingFormula.code,node_code,List.append_assoc]
theorem weighted_code (n : ℕ) (i : Fin (n+1)) : (weightFormula n i).code=weightedCode n i.val := by
  simp only [weightFormula,RingFormula.code,numerator_code,WeightCompiler.weight_code,weightedCode]
theorem generated_reference (n : ℕ) : generatedCode n=reference n := by
  simp only [reference,WeightCompiler.weighted_code,List.ofFn_eq_map,List.flatMap_map,
    Function.comp_def,weighted_code,totalFormula,WeightCompiler.totalDenominator_code]
  unfold generatedCode
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]

def numeratorFactor : Emits tripleUnary (fun x =>
    (if x.2=x.1.2 then [.one] else WeightCompiler.nodeCode false (x.2+1)++[.literal 2,.mul])++[.mul]) := by
  let factor := appendEmits ((thirdUnary.andThen successorComputes).andThen (nodeEmits false))
    (constantEmits tripleUnary [.literal 2,.mul])
  let chosen := ifEmits equalIndicesComputes (constantEmits tripleUnary [.one]) factor
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul])) (fun x => by simp)
def numeratorEmits : Emits pairUnary (fun x => numeratorCode x.1 x.2) :=
  appendEmits (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x => x.1+1) (firstUnary.andThen successorComputes) _ numeratorFactor)
def weightEmits : Emits pairUnary (fun x => weightedCode x.1 x.2) :=
  appendEmits (appendEmits numeratorEmits (WeightCompiler.weightEmits false))
    (constantEmits pairUnary [.mul])
def generatedEmits : Emits unary generatedCode :=
  appendEmits (appendEmits (appendEmits (constantEmits unary [.zero])
    (rangeEmits unary (fun n => n+1) successorComputes _
      (appendEmits weightEmits (constantEmits pairUnary [.copy 2,.mul,.add,.erase 1]))))
    (totalDenominatorEmits false)) (constantEmits unary [.swap])
def computes : Computes unary (Holant.OneHot.StackProgram.codeEncoding labels) reference :=
  recode (joinComputes generatedEmits (constantComputes unary Frame.wordEncoding [false])) id (fun _ => rfl)
    (fun n => by
      change chunk (generatedCode n)++[false]=framedListEncode (opEncoding labels) (reference n)
      rw [generated_reference]
      simpa only [chunk,List.append_nil,framedListEncode] using entries_append_encode (opEncoding labels) (reference n) [])

def numeratorSize (n : ℕ) : ℕ := (n+1)*(2*n+6)+1
def weightSize (n : ℕ) : ℕ := WeightFormulas.weightSize n+numeratorSize n+1
theorem numerator_size (n : ℕ) (i : Fin (n+1)) : (numeratorFormula n i).size≤numeratorSize n := by
  apply RingFormula.size_without_le _ _ (2*n+5)
  · omega
  · intro j
    simp only [RingFormula.size,WeightFormulas.node_size]
    have hj := j.isLt
    omega
theorem weight_size (n : ℕ) (i : Fin (n+1)) : (weightFormula n i).size≤weightSize n := by
  have h := WeightFormulas.weight_size_le false n i
  have hn := numerator_size n i
  simp only [weightFormula,RingFormula.size,weightSize]
  omega
theorem total_size (n : ℕ) : (totalFormula n).size≤weightSize n :=
  (WeightFormulas.totalDenominator_size_le false n).trans (by unfold weightSize; omega)

def structural (n Y : ℕ) : ℕ := (n+1)*(Y+weightSize n+1)
def structuralPolynomial (Y : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X+1)*(Y+
    ((Polynomial.X+1)*(2*((Polynomial.X+1)*Polynomial.X)+
      (Polynomial.X+1)*(4*Polynomial.X+10)+4)+1)+
    ((Polynomial.X+1)*(2*Polynomial.X+6)+1)+2)
theorem structural_eval (Y : Polynomial ℕ) (n : ℕ) :
    (structuralPolynomial Y).eval n=structural n (Y.eval n) := by
  simp [structuralPolynomial,structural,weightSize,numeratorSize,
    WeightFormulas.weightSize,WeightFormulas.denominatorSize] <;> ring

variable {d : ℕ} (F : FixedField ℚ d)
def coordinates : Fin 4 → Fin d → ℚ := fun a => F.decode.symm (coeff a)
theorem decode_coordinates (a : Fin 4) : F.decode (coordinates F a)=coeff a := F.decode.apply_symm_apply _
theorem decode_unit : F.decode (coordinates F 3)=1 := by rw [decode_coordinates]; rfl
theorem literal_bound (a : Fin 4) : ArithmeticSize.Bound (fun b => F.decode (coordinates F b)) 1 (coeff a) := by
  simpa only [decode_coordinates] using ArithmeticSize.Bound.coefficient (coeff := coeff) a
theorem count_bound (N Y : ℕ) (h : N≤2^Y) :
    ArithmeticSize.Bound (fun b => F.decode (coordinates F b)) Y (N : ℚ) := by
  refine ⟨N,fun _ _ => 3,h,?_⟩
  simp [decode_unit]

theorem trace_bound (n Y : ℕ) (y : Fin (n+1) → ℚ)
    (hy : ∀ i,ArithmeticSize.Bound (fun b => F.decode (coordinates F b)) Y (y i)) :
    ∀ x ∈ trace n y,ArithmeticSize.Bound (fun b => F.decode (coordinates F b)) (structural n Y) x := by
  have hw := Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.weighted_bound coeff
    (fun b => F.decode (coordinates F b)) 3 (decode_unit F) (literal_bound F)
    (List.ofFn (fun i => (weightFormula n i,y i))) Y (weightSize n) 0 0
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact weight_size n i)
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact hy i)
    (ArithmeticSize.Bound.zero 3 0)
  have hd := Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.formula_bound coeff
    (fun b => F.decode (coordinates F b)) 3 (decode_unit F) (literal_bound F) (totalFormula n)
  have hs : (totalFormula n).size≤structural n Y :=
    (total_size n).trans (by unfold structural; nlinarith)
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · simpa only [List.length_ofFn,zero_add,structural] using hw.2 x hx
  · exact (hd.2 x hx).mono 3 (decode_unit F) hs

def interpreter := StackInputInterpreter.machine
  (Kernels.machine (RingFormulaMachine.literals F (coordinates F)) (fieldProviders F))
    labels (RingFormulaMachine.labelBound labels)

def certified (n Y : ℕ) (y : Fin (n+1) → ℚ)
    (hy : ∀ i,ArithmeticSize.Bound (fun b => F.decode (coordinates F b)) Y (y i)) :
    Certified F.encoding (RingFormulaMachine.coefficients F (coordinates F))
      (ArithmeticSize.bitBound F (coordinates F) (structural n Y))
      (n+1+(reference n).length) (reference n) (List.ofFn y)
      [(resultPair n y).1,(resultPair n y).2] (trace n y) := by
  have hc : RingFormulaMachine.coefficients F (coordinates F)=coeff := by
    funext a
    exact decode_coordinates F a
  have hY : Y≤structural n Y := by unfold structural; nlinarith
  have hOne : 1≤structural n Y := by unfold structural; nlinarith
  rw [hc]
  exact certified_of_run F.encoding coeff
    (ArithmeticSize.bitBound F (coordinates F) (structural n Y)) (n+1+(reference n).length)
    (fun a => ((literal_bound F a).mono 3 (decode_unit F) hOne).encoded_length_le F (coordinates F))
    ((ArithmeticSize.Bound.zero 3 (structural n Y)).encoded_length_le F (coordinates F))
    ((ArithmeticSize.Bound.one.mono 3 (decode_unit F) (Nat.zero_le _)).encoded_length_le F (coordinates F))
    (reference n) (List.ofFn y) _ _ (reference_run n y)
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact ((hy i).mono 3 (decode_unit F) hY).encoded_length_le F (coordinates F))
    (fun x hx => (trace_bound F n Y y hy x hx).encoded_length_le F (coordinates F)) (by simp)

theorem execute (n Y : ℕ) (y : Fin (n+1) → ℚ)
    (hy : ∀ i,ArithmeticSize.Bound (fun b => F.decode (coordinates F b)) Y (y i)) :
    let W := ArithmeticSize.bitBound F (coordinates F) (structural n Y)
    ∃ t,t≤2*((Holant.OneHot.StackProgram.codeEncoding labels).encode (reference n)).length+
      2*((stackEncoding F.encoding).encode (List.ofFn y)).length+6+
      (reference n).length*Interpreter.instructionBound (RingFormulaMachine.labelBound labels)
        F.encoding (fieldProviders F) W (n+1+(reference n).length) ∧
      Kernels.Executes (interpreter F)
        (frame ((Holant.OneHot.StackProgram.codeEncoding labels).encode (reference n))++
          (stackEncoding F.encoding).encode (List.ofFn y))
        ((DivisionStack.encoding F).encode (resultPair n y)) t := by
  dsimp only
  exact StackInputInterpreter.execute labels (RingFormulaMachine.labelBound labels) F.encoding _
    (RingFormulaMachine.literals F (coordinates F)) (fieldProviders F) (RingFormulaMachine.label_le labels)
    (certified F n Y y hy)

end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Postprocess
