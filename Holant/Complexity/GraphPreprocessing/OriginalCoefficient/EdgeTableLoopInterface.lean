import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoopRun

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

/-- A faithful codec of raw-derived counter packages. The producer physically
creates both counts; this decoder also rejects inconsistent package fields. -/
def packageEncoding (s b : ℕ) (arity : ℕ → ℕ) :
    Encoding {r : RawClosedNetwork // r.WellFormed s b arity} Bool where
  encode x := CountsPackage.word x.val
  decode bits := do
    let (raw,rest) ← Holant.Algebraic.unframe bits
    let x ← (RawClosedNetwork.validatedEncoding s b arity).decode raw
    let (vertices,edges) ← Holant.Algebraic.unframe rest
    let v ← UnaryBinary.unaryEncoding.decode vertices
    let e ← UnaryBinary.unaryEncoding.decode edges
    if v=x.val.vertices.length ∧ e=x.val.edges.length then some x else none
  decode_encode x := by
    change (do
      let (raw,rest) ← Holant.Algebraic.unframe
        (Holant.Algebraic.frame ((RawClosedNetwork.validatedEncoding s b arity).encode x) ++
          (Holant.Algebraic.frame (UnaryBinary.unaryEncoding.encode x.val.vertices.length) ++
            UnaryBinary.unaryEncoding.encode x.val.edges.length))
      let r ← (RawClosedNetwork.validatedEncoding s b arity).decode raw
      let (vertices,edges) ← Holant.Algebraic.unframe rest
      let v ← UnaryBinary.unaryEncoding.decode vertices
      let e ← UnaryBinary.unaryEncoding.decode edges
      if v=r.val.vertices.length ∧ e=r.val.edges.length then some r else none) = some x
    simp [Holant.Algebraic.unframe_frame_append,Encoding.decode_encode]

def tableWord (x : {r : RawClosedNetwork // r.WellFormed s b arity}) : List Bool :=
  Holant.Algebraic.frame (List.replicate x.val.vertices.length true) ++
    ReachRound.encode (ReachRound.graphEdges (x.val.graph x.property))

noncomputable def timePolynomial (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word) : Polynomial ℕ :=
  Polynomial.X*(w.time.comp (3*(Polynomial.X+1))+10*Polynomial.X+10)+10*Polynomial.X+12

@[simp] theorem timePolynomial_eval (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word) (n : ℕ) :
    (timePolynomial w).eval n = n*(w.time.eval (3*(n+1))+10*n+10)+10*n+12 := by
  simp [timePolynomial]

theorem package_bound (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word)
    (r : RawClosedNetwork) :
    r.edges.length*roundBound w r+3*(RawClosedNetwork.encoding.encode r).length+
      4*r.vertices.length+2*r.edges.length+12 ≤ (timePolynomial w).eval (RawClosedNetwork.encoding.encode r).length := by
  have hc := r.counts_le_encoded_length
  have he : r.edges.length≤(RawClosedNetwork.encoding.encode r).length := by omega
  have hm := Nat.mul_le_mul_right (roundBound w r) he
  rw [timePolynomial_eval]
  change _ ≤ (RawClosedNetwork.encoding.encode r).length*roundBound w r+10*(RawClosedNetwork.encoding.encode r).length+12
  omega

theorem raw_length_le_package (x : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    (RawClosedNetwork.encoding.encode x.val).length ≤ ((packageEncoding s b arity).encode x).length := by
  change (RawClosedNetwork.encoding.encode x.val).length ≤ (CountsPackage.word x.val).length
  simp only [CountsPackage.word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate]
  omega

/-- The actual complete loop execution has polynomial cost in the genuine raw
input, even though its entry layout additionally holds physically derived counts. -/
noncomputable def timed_package (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word)
    (x : {r : RawClosedNetwork // r.WellFormed s b arity}) :
    TM2OutputsInTime (machine w.machine).computer ((packageEncoding s b arity).encode x) (some (tableWord x))
      ((timePolynomial w).eval (RawClosedNetwork.encoding.encode x.val).length) where
  steps := Classical.choose (package_run w x.val x.property)
  evals_in_steps := (Classical.choose_spec (package_run w x.val x.property)).2
  steps_le_m := le_trans (Classical.choose_spec (package_run w x.val x.property)).1 (package_bound w x.val)

noncomputable def computes (w : Computes (EdgeWord.inputEncoding s b arity) Frame.wordEncoding EdgeWord.word) :
    Computes (packageEncoding s b arity) Frame.wordEncoding tableWord where
  machine := machine w.machine
  time := timePolynomial w
  outputs x := {
    steps := (timed_package w x).steps
    evals_in_steps := (timed_package w x).evals_in_steps
    steps_le_m := le_trans (timed_package w x).steps_le_m
      (natPolynomial_eval_mono (timePolynomial w) (raw_length_le_package x)) }

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
