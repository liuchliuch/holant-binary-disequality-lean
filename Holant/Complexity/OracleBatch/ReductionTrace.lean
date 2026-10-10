import Holant.Complexity.OracleBatch.Reduction
import Holant.Complexity.OracleBatch.TraceExecution
import Holant.Complexity.OracleBatch.PrimitiveCost

namespace Holant.Complexity.OracleBatch
open Computability BinaryCompose FixedFieldMachines Holant.Algebraic
open UniversalPairReduction.ThreeQuery
variable {α β γ δ ε : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {eq : Encoding γ Bool} {ed : Encoding δ Bool} {ee : Encoding ε Bool}
  {pre : α → List γ × ε} {post : List δ × ε → β} {g : γ → δ}

/-- The public polynomial reduction has a valid bounded execution whose exact
ordered transcript is the preprocessor's complete encoded query list. -/
theorem reduction_run_trace (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle eq ed g oracle) (x : α) :
    ∃ n ≤ (reduction a b size).time.eval (ea.encode x).length,
      RunsTrace (reduction a b size).machine oracle
        ((reduction a b size).machine.init (ea.encode x))
        ((reduction a b size).machine.output (eb.encode (post (answers g (pre x)))))
        n ((pre x).1.map eq.encode) := by
  have hm := oracle_encoded_list oracle ho (pre x).1
  have ha : Turing.TM2OutputsInTime a.machine.computer (ea.encode x)
      (some (word ((pre x).1.map eq.encode) (ee.encode (pre x).2)))
      (a.time.eval (ea.encode x).length) := by
    simpa only [context_encode] using a.outputs x
  have hb : Turing.TM2OutputsInTime b.machine.computer
      (word (((pre x).1.map eq.encode).map oracle) (ee.encode (pre x).2))
      (some (eb.encode (post (answers g (pre x)))))
      (b.time.eval ((contextEncoding ed ee).encode (answers g (pre x))).length) := by
    simpa only [context_encode,answers,hm] using b.outputs (answers g (pre x))
  have hr := run_trace a.machine b.machine oracle (ea.encode x) ((pre x).1.map eq.encode)
    (ee.encode (pre x).2) (eb.encode (post (answers g (pre x)))) ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  refine ⟨_,?_,hr⟩
  have hp := a.outputBound.length_le x
  have hd := decoder_length_le a size x
  have ht := natPolynomial_eval_mono b.time hd
  have hc := overhead_le oracle ((pre x).1.map eq.encode) (ee.encode (pre x).2)
  have hat := ha.steps_le_m
  have hbt := hb.steps_le_m
  rw [context_encode] at hp
  simp only [context_encode,answers] at hd
  simp only [overhead] at hc
  have hdq : (word (((pre x).1.map eq.encode).map oracle) (ee.encode (pre x).2)).length ≤
      (decoderBound a size).eval (ea.encode x).length := by
    simpa only [hm] using hd
  simp only [reduction,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_comp]
  omega

/-- Actual oracle count equals list length, with primitive-operation cost bounded
by an explicit original-input polynomial times the fixed program budget. -/
theorem reduction_query_count (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle eq ed g oracle) (x : α) :
    ∃ n ≤ (reduction a b size).time.eval (ea.encode x).length,
      (fun p => p.bind ((reduction a b size).machine.step oracle))^[n]
        (some ((reduction a b size).machine.init (ea.encode x))) =
        some ((reduction a b size).machine.output (eb.encode (post (answers g (pre x))))) ∧
      queryCount (reduction a b size).machine oracle
        ((reduction a b size).machine.init (ea.encode x)) n = (pre x).1.length ∧
      primitiveCount (reduction a b size).machine oracle
        ((reduction a b size).machine.init (ea.encode x)) n ≤
        (Polynomial.C (reduction a b size).machine.primitiveBudget *
          (reduction a b size).time).eval (ea.encode x).length := by
  rcases reduction_run_trace a b size oracle ho x with ⟨n,hn,hr⟩
  refine ⟨n,hn,hr.run,?_,?_⟩
  · simpa only [List.length_map] using hr.count
  · have hc := primitiveCount_le (reduction a b size).machine oracle
      ((reduction a b size).machine.init (ea.encode x)) n
    exact le_trans hc (by
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
        Nat.mul_le_mul_left (reduction a b size).machine.primitiveBudget hn)

/-- Input-dependent interpolation with m+1 samples uses the same one machine. -/
theorem reduction_query_count_succ (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle eq ed g oracle)
    (m : α → ℕ) (hlen : ∀ x, (pre x).1.length = m x + 1) (x : α) :
    ∃ n ≤ (reduction a b size).time.eval (ea.encode x).length,
      queryCount (reduction a b size).machine oracle
        ((reduction a b size).machine.init (ea.encode x)) n = m x + 1 := by
  rcases reduction_query_count a b size oracle ho x with ⟨n,hn,_,hq,_⟩
  exact ⟨n,hn,hq.trans (hlen x)⟩

/-- All prefixes on a valid encoded input are bounded by its actual list length,
including prefixes extending beyond the completed decoder. -/
theorem reduction_prefix_count (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle eq ed g oracle) (x : α) (n : ℕ) :
    queryCount (reduction a b size).machine oracle
      ((reduction a b size).machine.init (ea.encode x)) n ≤ (pre x).1.length := by
  rcases reduction_run_trace a b size oracle ho x with ⟨time,_,hr⟩
  simpa only [List.length_map] using hr.prefix_count_le n

/-- Naming the computed source function leaves the literal transcript intact. -/
theorem of_eq_run_trace (a : Computes ea (contextEncoding eq ee) pre)
    (b : Computes (contextEncoding ed ee) eb post) (size : PolynomialOutputBound eq ed g)
    (f : α → β) (heq : ∀ x, f x = post (answers g (pre x)))
    (oracle : List Bool → List Bool) (ho : RepresentsOracle eq ed g oracle) (x : α) :
    ∃ n ≤ (of_eq a b size f heq).time.eval (ea.encode x).length,
      RunsTrace (of_eq a b size f heq).machine oracle
        ((of_eq a b size f heq).machine.init (ea.encode x))
        ((of_eq a b size f heq).machine.output (eb.encode (f x)))
        n ((pre x).1.map eq.encode) := by
  simpa only [of_eq,heq x] using reduction_run_trace a b size oracle ho x

end Holant.Complexity.OracleBatch
