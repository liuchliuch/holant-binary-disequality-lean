import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.OptionChoiceInterface

/-! Typed optional-value defaulting using the existing
physical tag/parser/copy program. Reinterpret only equal encoded bytes; no
semantic decoding or arbitrary field operation is introduced as a primitive. -/

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.OptionalValue
open Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
open Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section
variable {A : Type} (ea : Encoding A Bool) (fallback : A)

def chooseComputes : Computes (pairEncoding (optionEncoding ea) (optionEncoding ea)) ea
    (fun q : Option A × Option A => q.1.getD (q.2.getD fallback)) := by
  apply recode (OptionChoice.computes (ea.encode fallback))
    (fun q : Option A × Option A => (q.1.map ea.encode,q.2.map ea.encode))
  · intro q
    rcases q with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  · intro q
    rcases q with ⟨a,b⟩
    cases a <;> cases b <;> rfl

def getDComputes : Computes (optionEncoding ea) ea (fun q => q.getD fallback) :=
  (pairComputes (identityComputes (optionEncoding ea))
    (constantComputes (optionEncoding ea) (optionEncoding ea) none)).andThen
      (chooseComputes ea fallback)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Support.OptionalValue
