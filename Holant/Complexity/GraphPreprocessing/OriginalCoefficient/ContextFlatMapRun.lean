import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapFinish

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def ticks {A : Type} (e : Encoding A Bool) (context : List Bool) (f : A → List Bool) (steps : A → ℕ) (xs : List A) :=
  (xs.map (fun a => steps a+4*context.length+2*(e.encode a).length+(f a).length+9)).sum

/-- Exact original-order flat concatenation, preserving an arbitrary accumulated
word and output suffix. Every provider is called once for its physical entry. -/
theorem loop {A : Type} (e : Encoding A Bool) (context : List Bool) (f : A → List Bool) (steps : A → ℕ)
    (xs : List A) (rev out : List Bool)
    (h : ∀ a∈xs, (fun c => c.bind m.computer.step)^[steps a]
      (some (initList m.computer (Holant.Algebraic.frame context++e.encode a)))=some (haltList m.computer (f a))) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 2) (framedListEncode e xs) context rev out)
      (ready m (.inr 2) [false] context ((xs.flatMap f).reverse++rev) out) (ticks e context f steps xs) := by
  induction xs generalizing rev with
  | nil => simp [ticks,framedListEncode,RunsExactly]
  | cons a xs ih =>
    have first := round m context (framedListEncode e xs) rev out (e.encode a) (f a) (steps a) (h a (by simp))
    have last := ih ((f a).reverse++rev) (fun b hb => h b (by simp [hb]))
    have all := first.trans last
    simpa [ticks,framedListEncode,List.reverse_append,List.append_assoc,Nat.add_comm] using all

theorem whole {A : Type} (e : Encoding A Bool) (context : List Bool) (f : A → List Bool) (steps : A → ℕ)
    (xs : List A)
    (h : ∀ a∈xs, (fun c => c.bind m.computer.step)^[steps a]
      (some (initList m.computer (Holant.Algebraic.frame context++e.encode a)))=some (haltList m.computer (f a))) :
    RunsExactly (machine m).computer.step
      (initList (machine m).computer (Holant.Algebraic.frame context++framedListEncode e xs))
      (haltList (machine m).computer (xs.flatMap f))
      (ticks e context f steps xs+3*context.length+(xs.flatMap f).length+7) := by
  have middle := loop m e context f steps xs [] [] h
  simp only [List.append_nil] at middle
  have all := ((prepare m context (framedListEncode e xs)).trans middle).trans
    (finish m context (xs.flatMap f).reverse)
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at all
  rw [initial]
  have ht : ticks e context f steps xs+3*context.length+(xs.flatMap f).length+7=
      (context.length+(xs.flatMap f).length+5)+(ticks e context f steps xs+2*(context.length+1)) := by omega
  rw [ht]
  exact all
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
