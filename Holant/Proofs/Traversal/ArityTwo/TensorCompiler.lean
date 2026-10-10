import Holant.Proofs.Traversal.ArityTwo.TensorTemplates
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.Complexity.FixedGadgetSubstitution.Size


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorCompiler
open Holant Holant.Complexity Holant.Tractable Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution TensorTemplates
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} (family : Fin s → AnySignature AlgebraicComplex)
variable (hf : ∀ i, SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) (family i).2)
variable (b : ℕ)

def hypotheses : ∀ j < s,
    (templates family hf b j).WellFormed (size family hf) b (arity family hf) ∧
      (templates family hf b j).boundary = originalArity family hf b j :=
  fun j hj => ⟨templates_wellFormed family hf b j hj,rfl⟩

abbrev Input := Compiler.Input s b (originalArity family hf b)
abbrev Output := Compiler.Input (size family hf) b (arity family hf)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s b (originalArity family hf b)
abbrev outputEncoding := RawClosedNetwork.validatedEncoding (size family hf) b (arity family hf)

def value : Input family hf b → Output family hf b :=
  Compiler.value s b (originalArity family hf b) (templates family hf b)
    (size family hf) (arity family hf) (hypotheses family hf b)

def computes : Computes (inputEncoding family hf b) (outputEncoding family hf b)
    (value family hf b) :=
  Compiler.computes s b (originalArity family hf b) (templates family hf b)
    (size family hf) (arity family hf) (hypotheses family hf b)

theorem inFP : InFP (inputEncoding family hf b) (outputEncoding family hf b) (value family hf b) :=
  (computes family hf b).inFP

theorem degree_le (r : Input family hf b) (v : Fin (value family hf b r).val.vertices.length) :
    arity family hf ((value family hf b r).val.vertices.get v).1 ≤ 2 :=
  arity_le family hf ((value family hf b r).val.signatureLabel (value family hf b r).property v)

/-- The equation is for the actual raw graph emitted by the compiler, retaining
all original edge kernels, self-loops, parallel edges and scalar occurrences. -/
theorem denote (r : Input family hf b) (edges : Fin b → Kernel AlgebraicComplex) :
    ((value family hf b r).val.realize (value family hf b r).property
      (signatures family hf) edges).denote Fin.elim0 =
    (r.val.realize r.property (originalSignatures family hf b) edges).denote Fin.elim0 := by
  have h := replacement_partition (templates family hf b) r.val r.property
    (templates_wellFormed family hf b) (originalSignatures family hf b)
    (signatures family hf) edges (fun _ => 1)
    (by intro i; simpa using templates_exact family hf b i edges)
  simpa [value,Compiler.value] using h

def vertexBound : ℕ := ∑ i : Fin s, (template family hf b i).vertices.length

theorem template_bounds (j : ℕ) (hj : j < s) :
    (templates family hf b j).vertices.length ≤ vertexBound family hf b ∧
      (templates family hf b j).edges.length ≤ 0 := by
  have hv : (template family hf b ⟨j,hj⟩).vertices.length ≤ vertexBound family hf b :=
    Finset.single_le_sum (f := fun i : Fin s => (template family hf b i).vertices.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j,hj⟩ : Fin s))
  constructor
  · simpa only [templates,dif_pos hj] using hv
  · have he := template_edges family hf b ⟨j,hj⟩
    simpa only [templates,dif_pos hj,he,List.length_nil] using (Nat.le_refl 0)

def sizePolynomial := querySizePolynomial (size family hf) b 2 (vertexBound family hf b) 0

theorem encoded_length (r : Input family hf b) :
    (RawClosedNetwork.encoding.encode (value family hf b r).val).length ≤
      (sizePolynomial family hf b).eval (RawClosedNetwork.encoding.encode r.val).length :=
  replace_length_le (templates family hf b) r.val r.property (hypotheses family hf b)
    2 (vertexBound family hf b) 0 (fun j hj => arity_le family hf ⟨j,hj⟩)
    (template_bounds family hf b)

/-- The same run and same physical input bytes as `computes`; the instruction
budget includes transfer and output, not only semantic substitution counts. -/
theorem primitive_bound (r : Input family hf b) :
    let w := computes family hf b
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes family hf b) r

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorCompiler
