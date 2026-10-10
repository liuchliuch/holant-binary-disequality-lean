import Holant.Proofs.Traversal.MatchingExpansion.Templates
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.Complexity.FixedGadgetSubstitution.Size


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Compiler
open Holant Holant.Tractable Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (opposite : Bool) (hf : ∀ i, SourceTensorClosure (matchingImage opposite) (G i))

abbrev Input := FixedGadgetSubstitution.Compiler.Input s 1 a
abbrev Output := FixedGadgetSubstitution.Compiler.Input (Templates.size G opposite hf) 1 (Templates.arity G opposite hf)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev outputEncoding := RawClosedNetwork.validatedEncoding (Templates.size G opposite hf) 1 (Templates.arity G opposite hf)

def value : Input (s:=s) (a:=a) → Output G opposite hf :=
  FixedGadgetSubstitution.Compiler.value s 1 a (Templates.templates G opposite hf)
    (Templates.size G opposite hf) (Templates.arity G opposite hf) (Templates.hypotheses G opposite hf)

def computes : Computes inputEncoding (outputEncoding G opposite hf) (value G opposite hf) :=
  FixedGadgetSubstitution.Compiler.computes s 1 a (Templates.templates G opposite hf)
    (Templates.size G opposite hf) (Templates.arity G opposite hf) (Templates.hypotheses G opposite hf)

theorem denote (r : Input (s:=s) (a:=a)) :
    ((value G opposite hf r).val.realize (value G opposite hf r).property
      (Templates.signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 =
        (r.val.realize r.property G (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 := by
  let r' := RawArityTransport.input (Templates.arityAgree G opposite hf) r
  have h := replacement_partition (Templates.templates G opposite hf) r'.val r'.property
    (fun j hj => (Templates.hypotheses G opposite hf j hj).1)
    (RawArityTransport.signatures (Templates.arityAgree G opposite hf) (Orientation.transformed G opposite))
    (Templates.signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality) (fun _ => 1)
    (by intro i; simpa using Templates.templates_exact G opposite hf i)
  calc
    _ = (r'.val.realize r'.property
        (RawArityTransport.signatures (Templates.arityAgree G opposite hf) (Orientation.transformed G opposite))
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 := by
      simpa [value,FixedGadgetSubstitution.Compiler.value,r',RawArityTransport.input] using h
    _ = (r.val.realize r.property (Orientation.transformed G opposite)
        (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 :=
      RawArityTransport.denote (Templates.arityAgree G opposite hf) (Orientation.transformed G opposite) _ r
    _ = _ := Orientation.denote G opposite r

def arityBound : ℕ := ∑ i : Fin (Templates.size G opposite hf), Templates.arity G opposite hf i.val
def vertexBound : ℕ := ∑ i : Fin s, (Templates.template G opposite hf i).vertices.length
theorem arity_le (j : ℕ) (hj : j<Templates.size G opposite hf) :
    Templates.arity G opposite hf j ≤ arityBound G opposite hf :=
  Finset.single_le_sum (f:=fun i : Fin (Templates.size G opposite hf) => Templates.arity G opposite hf i.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j,hj⟩ : Fin (Templates.size G opposite hf)))
theorem template_bounds (j : ℕ) (hj : j<s) :
    (Templates.templates G opposite hf j).vertices.length ≤ vertexBound G opposite hf ∧
      (Templates.templates G opposite hf j).edges.length ≤ 0 := by
  have h : (Templates.template G opposite hf ⟨j,hj⟩).vertices.length ≤ vertexBound G opposite hf :=
    Finset.single_le_sum (f:=fun i : Fin s => (Templates.template G opposite hf i).vertices.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j,hj⟩ : Fin s))
  simpa only [Templates.templates,dif_pos hj,Templates.template_edges,List.length_nil] using And.intro h (Nat.le_refl 0)
def sizePolynomial := querySizePolynomial (Templates.size G opposite hf) 1
  (arityBound G opposite hf) (vertexBound G opposite hf) 0
theorem encoded_length (r : Input (s:=s) (a:=a)) :
    (RawClosedNetwork.encoding.encode (value G opposite hf r).val).length ≤
      (sizePolynomial G opposite hf).eval (RawClosedNetwork.encoding.encode r.val).length :=
  replace_length_le (Templates.templates G opposite hf) r.val r.property (Templates.hypotheses G opposite hf)
    _ _ _ (arity_le G opposite hf) (template_bounds G opposite hf)

theorem primitive_bound (r : Input (s:=s) (a:=a)) :
    let w := computes G opposite hf
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
        (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes G opposite hf) r

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Compiler
