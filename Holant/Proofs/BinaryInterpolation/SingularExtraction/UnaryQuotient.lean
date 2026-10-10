import Holant.Proofs.BinaryInterpolation.SingularExtraction.ResidueMachine


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.UnaryQuotient
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (k : ℕ) (hk : 0 < k)

def token (i : ℕ) : List Bool := if k ∣ i+1 then [true] else []

include hk in
theorem tokens (n : ℕ) : (List.range n).flatMap (token k) = List.replicate (n/k) true := by
  induction n with
  | zero => simp [token]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases h : k ∣ n+1
    · simp [token, h, Nat.succ_div, hk.ne', List.replicate_add]
    · simp [token, h, Nat.succ_div, hk.ne']

def tokenComputes (hk : 0 < k) : Computes UnaryBinary.unaryEncoding Frame.wordEncoding (token k) := by
  let f : Fin k → List Bool := fun r => if (r.val+1)%k=0 then [true] else []
  refine congrComputes (ResidueMachine.computes k hk Frame.wordEncoding f) ?_
  intro i
  have h : ((i%k)+1)%k = (i+1)%k := by simp [Nat.add_mod]
  simp only [f, ResidueMachine.remainder, token]
  simp only [h, Nat.dvd_iff_mod_eq_zero]

/-- Actual floor division; the output is a unary counter, not a free natural
register. ContextFlatMap charges every invocation and output token. -/
def computes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n => n/k) := by
  let provider : Computes (sigmaEncoding Frame.wordEncoding (fun _ => UnaryBinary.unaryEncoding))
      Frame.wordEncoding (fun x => token k x.2) :=
    recode ((Wiring.secondComputes Frame.wordEncoding UnaryBinary.unaryEncoding).andThen
      (tokenComputes k hk)) (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  let prepare : Computes UnaryBinary.unaryEncoding
      (ContextFlatMap.inputEncoding Frame.wordEncoding (fun _ => UnaryBinary.unaryEncoding))
      (fun n => (⟨[],List.range n⟩ : Σ _ : List Bool,List ℕ)) :=
    recode (pairComputes (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding [])
      ComponentSelection.UnaryRange.computes) id (fun _ => rfl) (fun _ => rfl)
  exact recode (prepare.andThen (ContextFlatMap.computes Frame.wordEncoding
    (fun _ => UnaryBinary.unaryEncoding) _ provider)) id (fun _ => rfl)
      (fun n => tokens k hk n)

def timesComputes : (m : ℕ) → Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
    (fun n => m*n)
  | 0 => by simpa only [Nat.zero_mul] using
      (constantComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding 0)
  | m+1 => recode (joinComputes ((timesComputes m).andThen (encodeComputes UnaryBinary.unaryEncoding))
      (encodeComputes UnaryBinary.unaryEncoding)) id (fun _ => rfl)
      (fun n => by simp only [UnaryBinary.unaryEncoding, Frame.wordEncoding, id_eq, Function.comp_apply, Nat.succ_mul, List.replicate_add])

def addConstantComputes (c : ℕ) : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
    (fun n => n+c) :=
  recode (joinComputes (encodeComputes UnaryBinary.unaryEncoding)
    (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding (List.replicate c true)))
    id (fun _ => rfl) (fun n => by simp only [UnaryBinary.unaryEncoding, Frame.wordEncoding, id_eq, Function.comp_apply, List.replicate_add])

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.UnaryQuotient
