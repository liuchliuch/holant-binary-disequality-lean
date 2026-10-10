import Holant.Complexity.FixedGadgetSubstitution.Compiler.Template
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix

/-! A fixed finite family of candidate programs followed by a real indexed
selection. The number of candidates is part of finite program syntax. Runtime
selection reads the original source label; no host-level dynamic dispatch or
precomputed expansion is supplied as input. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {A B : Type}
noncomputable def chooseComputes (ea : Encoding A Bool) (eb : Encoding B Bool) (n : ℕ)
    (label : A → Fin n) (f : A → Fin n → B)
    (index : Computes ea UnaryBinary.unaryEncoding (fun a => (label a).val))
    (w : ∀ i, Computes ea eb (fun a => f a i)) :
    Computes ea eb (fun a => f a (label a)) := by
  let output (a : A) := (List.finRange n).map (f a)
  let selectedIndex (a : A) : Fin (output a).length := ⟨(label a).val,by simpa [output] using (label a).isLt⟩
  let prepare : Computes ea (ParentRowSelect.inputEncoding eb)
      (fun a => ⟨output a,selectedIndex a⟩) :=
    recode (pairComputes (fixedListComputes ea eb f w (List.finRange n)) index)
      id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (ParentRowSelect.computes eb))
    (fun a => by simp [ParentRowSelect.selected,output,selectedIndex,List.get_eq_getElem])
variable (s b : ℕ) (arity : ℕ → ℕ)
noncomputable def placementComputes (templates : ℕ → Template) :
    Computes (queryEncoding s b arity) placementEncoding
      (fun x => (rowOffset s b arity templates x,(x.1.val.vertices.get x.2).2)) :=
  pairComputes (offsetComputes s b arity templates)
    ((originalRowComputes s b arity).andThen
      (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
        id (fun _ => rfl) (fun _ => rfl)))
def vertexChunk (templates : ℕ → Template) (x : Query s b arity) : List Bool :=
  entries vertexEncoding ((templates (x.1.val.vertices.get x.2).1).placeVertices
    (rowOffset s b arity templates x) (x.1.val.vertices.get x.2).2)
noncomputable def vertexChunkComputes (templates : ℕ → Template) :
    Computes (queryEncoding s b arity) Frame.wordEncoding (vertexChunk s b arity templates) :=
  chooseComputes (queryEncoding s b arity) Frame.wordEncoding s (sourceLabel s b arity)
    (fun x label => entries vertexEncoding ((templates label.val).placeVertices
      (rowOffset s b arity templates x) (x.1.val.vertices.get x.2).2))
    (labelRecodeComputes s b arity UnaryBinary.unaryEncoding Fin.val)
    (fun label => (placementComputes s b arity templates).andThen (templateEntriesComputes (templates label.val)))
noncomputable def edgeChunkComputes (templates : ℕ → Template) :
    Computes (queryEncoding s b arity) Frame.wordEncoding
      (fun x => entries encodingNatBool (templates (x.1.val.vertices.get x.2).1).edges) :=
  labelRecodeComputes s b arity Frame.wordEncoding (fun label => entries encodingNatBool (templates label.val).edges)
end Holant.Complexity.FixedGadgetSubstitution.Compiler
