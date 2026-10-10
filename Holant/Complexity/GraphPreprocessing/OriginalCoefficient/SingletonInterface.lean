import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonRecode
import Holant.Complexity.ClosedNetworkSemantics

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false

def label (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    RawClosedNetwork.TreeLabel s b arity := OccurrenceLabel.literal ⟨r.signatureLabel h p.1, some p.2⟩

@[simp] theorem label_eq (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) :
    label r h p = some (.inl ⟨r.signatureLabel h p.1, fun j => decide (j = p.2)⟩) := rfl

def ticks (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) (p : r.Ports arity) : ℕ :=
  VertexSignature.originalTicks r p.1 + 2 * p.2.val + 2 * (encodeNat (r.vertices.get p.1).1).length +
    2 * ((treeLabelEncoding s b arity).encode (label r h p)).length + if framed then 12 else 11

/-- The original signature ID is physically extracted; the preserved local port
is copied and checked against its fixed arity before the exact label is emitted. -/
theorem exact_run (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (p : r.Ports arity) (output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (sourceLabel s arity (.inr 0)) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate p.1.val true) (List.replicate p.2.val true) [] [] [] output))
      (cfg (phase s arity 7) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate p.1.val true) (List.replicate p.2.val true) [] [] []
        (outputWord framed ((treeLabelEncoding s b arity).encode (label r h p)) ++ output)))
      (ticks framed r h p) := by
  let raw := RawClosedNetwork.encoding.encode r
  let query := List.replicate p.1.val true
  let port := List.replicate p.2.val true
  have first := extract s b arity framed r p.1 port output
  have second := prepare s b arity framed raw query port (encodeNat (r.vertices.get p.1).1) output
  have third := recode s b arity framed (r.signatureLabel h p.1) p.2 raw query output
  have last := emit s b arity framed raw query port ((treeLabelEncoding s b arity).encode (label r h p)) output
  have all := ((first.trans second).trans third).trans last
  convert all using 1
  dsimp only [ticks, emitTicks, port]
  cases framed <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_replicate] <;> omega

theorem ticks_le (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (p : r.Ports arity) :
    ticks framed r h p ≤ 12 * ((RawClosedNetwork.encoding.encode r).length + 1) +
      2 * maxArity s arity + 2 * s.size + 2 * lengthBound s b arity + 12 := by
  have hv := VertexSignature.originalTicks_le r p.1
  have hs := SignatureLabel.binaryFinEncoding_length_le s (r.signatureLabel h p.1)
  change (encodeNat (r.vertices.get p.1).1).length ≤ s.size at hs
  have hl := treeLabelEncoding_length_le s b arity (label r h p)
  have hp := p.2.isLt
  have ha := arity_le_maxArity arity (r.signatureLabel h p.1)
  change arity (r.vertices.get p.1).1 ≤ maxArity s arity at ha
  unfold ticks
  cases framed <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonLabel
