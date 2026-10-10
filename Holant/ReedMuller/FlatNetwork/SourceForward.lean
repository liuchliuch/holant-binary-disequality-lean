import Holant.ReedMuller.FlatNetwork.OpenNetwork

/-! Source Lemma 7.14, item 1, with the exact RM/repetition affine vertex
families. The converse and its physical size bound remain separate. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def scaledFlat (c : ℂ) (a : BinaryVector n) (D : BinaryCode n) : Signature ℂ n :=
  fun x => if (fun i => bit (x i)-a i)∈D then c else 0

theorem scaledFlat_flatOrZero (c : ℂ) (a : BinaryVector n) (D : BinaryCode n) (hD : SelfDual D) :
    FlatOrZero (scaledFlat c a D) := by
  by_cases hc : c=0
  · left;subst c;funext x;simp [scaledFlat]
  · right;exact ⟨Units.mk0 c hc,a,D,hD,rfl⟩

/-- Exactly the affine shifted/scaled RM and repetition tables in item 1.
A zero proportionality coefficient is also covered by the explicit zero branch. -/
inductive SourcePrimitive : {n : ℕ} → Signature ℂ n → Prop
  | rm (c : ℂ) (a : BinaryVector 8) : SourcePrimitive (scaledFlat c a CoefficientAtlas.code)
  | binary (c : ℂ) (a : BinaryVector 2) : SourcePrimitive (scaledFlat c a repetitionCode)

theorem SourcePrimitive.flatOrZero {f : Signature ℂ n} (hf : SourcePrimitive f) : FlatOrZero f := by
  cases hf with
  | rm c a => exact scaledFlat_flatOrZero c a _ CoefficientAtlas.code_selfDual
  | binary c a => exact scaledFlat_flatOrZero c a _ repetitionCode_selfDual

/-- The full source forward assertion applies to corrected OpenNetwork tensors,
not to an assumed expression tree or only ordinary-boundary networks. -/
theorem source_flat_network_forward (N : OpenNetwork ℂ n) (hv : ∀ v,SourcePrimitive (N.vertex v)) :
    N.tensor=0 ∨ ∃ (c : ℂˣ) (a : BinaryVector n) (D : BinaryCode n),
      SelfDual D ∧ N.tensor=flatSignature c a D :=
  open_network_flatOrZero N (fun v => (hv v).flatOrZero)

theorem source_flat_network_even (N : OpenNetwork ℂ n) (hv : ∀ v,SourcePrimitive (N.vertex v))
    (hn : N.tensor≠0) : Even n :=
  open_network_boundary_even N (fun v => (hv v).flatOrZero) hn

end
end Holant.ReedMuller.FlatNetwork
