import Holant.Proofs.Algorithms.TransformRecognition.RawAffineFamilyEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRowsSource
import Mathlib.Data.List.Forall2


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineCandidateSource
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver (mem_cross)
variable {s : ℕ} (arity : Fin s → ℕ)

def generated (input : OriginalFamilyInput.Input arity) : List RawAffineBranchMachine.Templates :=
  RawAffineFamilyEnumeration.candidates (OriginalCatalogueSource.family arity input)
def vertex (c : RawAffineBranchMachine.Templates) (i : Fin s) : EncodedTable.Data :=
  c.1.getD i.val RawAffineBranchMachine.emptyTemplate

theorem choices_exact (input : OriginalFamilyInput.Input arity) :
    RawAffineFamilyEnumeration.choices (OriginalCatalogueSource.family arity input) =
      List.ofFn (fun i => RawAffineEnumeration.templates (arity i)) := by
  simp only [RawAffineFamilyEnumeration.choices,OriginalCatalogueSource.family,
    OriginalFamilyPackingSource.fromSource,List.map_map,Function.comp_def,List.ofFn_eq_map]

theorem vertex_relation (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) :
    List.Forall₂ (fun xs d => d ∈ xs)
      (List.ofFn (fun i => RawAffineEnumeration.templates (arity i))) c.1 := by
  have h := (RawAffineFamilyEnumeration.mem_product_iff _ _).mp (mem_cross.mp hc).1
  rwa [choices_exact] at h

theorem vertex_length (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) : c.1.length=s := by
  have h := (vertex_relation arity input c hc).length_eq
  simpa only [List.length_ofFn] using h.symm

theorem vertex_generated (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) (i : Fin s) :
    vertex c i ∈ RawAffineEnumeration.templates (arity i) := by
  have h := vertex_relation arity input c hc
  have hi : i.val<c.1.length := by rw [vertex_length arity input c hc]; exact i.isLt
  have hl : i.val<(List.ofFn (fun i => RawAffineEnumeration.templates (arity i))).length := by
    simpa only [List.length_ofFn] using i.isLt
  have hg := h.get hl hi
  simpa only [vertex,List.getD_eq_getElem c.1 RawAffineBranchMachine.emptyTemplate hi,List.get_eq_getElem,List.getElem_ofFn] using hg

theorem vertex_regular (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) (i : Fin s) :
    (vertex c i).1=arity i ∧ EncodedTable.Regular (vertex c i) :=
  RawAffineEnumerationValidity.generated_regular (arity i) (vertex c i) (vertex_generated arity input c hc i)

theorem edge_regular (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) :
    c.2.1=2 ∧ EncodedTable.Regular c.2 :=
  RawAffineEnumerationValidity.generated_regular 2 c.2 (mem_cross.mp hc).2

def normalizeAt (n : ℕ) (d : EncodedTable.Data) (hd : d.1=n) : AffineNormalForm.Code n :=
  hd ▸ RawAffineTemplateNormalization.normalize d

def normalized (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) : AffineBranch.Branch arity :=
  ((fun i => normalizeAt (arity i) (vertex c i) (vertex_regular arity input c hc i).1),
    normalizeAt 2 c.2 (edge_regular arity input c hc).1)

theorem coefficient_at {n v : ℕ} (imaginary : Fin v) (d : EncodedTable.Data)
    (hdim : d.1=n) (hd : EncodedTable.Regular d) (x : Fin n → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,d,List.ofFn x)=
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.affineCoefficient imaginary (normalizeAt n d hdim) x) := by
  subst n
  exact RawAffineTemplateNormalization.coefficient_exact imaginary d hd x

theorem vertex_coefficient {v : ℕ} (imaginary : Fin v) (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input)
    (i : Fin s) (x : Fin (arity i) → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,vertex c i,List.ofFn x)=
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.affineCoefficient imaginary
        ((normalized arity input c hc).1 i) x) :=
  coefficient_at imaginary (vertex c i) (vertex_regular arity input c hc i).1
    (vertex_regular arity input c hc i).2 x

theorem edge_coefficient {v : ℕ} (imaginary : Fin v) (input : OriginalFamilyInput.Input arity)
    (c : RawAffineBranchMachine.Templates) (hc : c ∈ generated arity input) (x : Fin 2 → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,c.2,List.ofFn x)=
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.affineCoefficient imaginary
        (normalized arity input c hc).2 x) :=
  coefficient_at imaginary c.2 (edge_regular arity input c hc).1
    (edge_regular arity input c hc).2 x

end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineCandidateSource
