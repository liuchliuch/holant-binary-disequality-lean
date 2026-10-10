import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertexRecode
import Holant.Complexity.ClosedNetworkSemantics
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Original-vertex coefficient emission from literal residual pin bytes. The
pin producer has an explicit separate physical interface; the stored signature
ID is always extracted from the preserved original raw network. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertex
open Turing Computability StackProtocol BinaryCompose
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false

def label (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (d : ResidualLabel.Descriptor (arity (r.vertices.get v).1)) : RawClosedNetwork.TreeLabel s b arity :=
  ResidualLabel.literal ⟨r.signatureLabel h v,d⟩

def descriptorWord (r : RawClosedNetwork) (v : Fin r.vertices.length)
    (d : ResidualLabel.Descriptor (arity (r.vertices.get v).1)) : List Bool :=
  (ResidualLabel.descriptorEncoding (arity (r.vertices.get v).1)).encode d

def ticks (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (d : ResidualLabel.Descriptor (arity (r.vertices.get v).1)) : ℕ :=
  VertexSignature.originalTicks r v + 2 * (descriptorWord r v d).length +
    2 * (encodeNat (r.vertices.get v).1).length + 2 * ((treeLabelEncoding s b arity).encode (label r h v d)).length +
      if framed then 11 else 10

/-- Exact residual assignment table label, retaining every caller input and output suffix. -/
theorem exact_run (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (d : ResidualLabel.Descriptor (arity (r.vertices.get v).1)) (output : List Bool) :
    RunsExactly (machine s b arity framed).computer.step
      (cfg (sourceLabel s arity (.inr 0)) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) (descriptorWord r v d) [] [] [] output))
      (cfg (phase s arity 7) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) (descriptorWord r v d) [] [] []
        (outputWord framed ((treeLabelEncoding s b arity).encode (label r h v d)) ++ output)))
      (ticks framed r h v d) := by
  let raw := RawClosedNetwork.encoding.encode r
  let query := List.replicate v.val true
  let descriptor := descriptorWord r v d
  have first := extract s b arity framed r v descriptor output
  have second := prepare s b arity framed raw query descriptor (encodeNat (r.vertices.get v).1) output
  have third := recode s b arity framed (r.signatureLabel h v) d raw query output
  have last := emit s b arity framed raw query descriptor ((treeLabelEncoding s b arity).encode (label r h v d)) output
  have all := ((first.trans second).trans third).trans last
  convert all using 1
  dsimp only [ticks,emitTicks,descriptor]
  cases framed <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem ticks_le (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (d : ResidualLabel.Descriptor (arity (r.vertices.get v).1)) :
    ticks framed r h v d ≤ 12 * ((RawClosedNetwork.encoding.encode r).length + 1) +
      2 * ResidualLabel.inputBound s arity + 2 * s.size + 2 * lengthBound s b arity + 11 := by
  have hv := VertexSignature.originalTicks_le r v
  have hs := SignatureLabel.binaryFinEncoding_length_le s (r.signatureLabel h v)
  change (encodeNat (r.vertices.get v).1).length ≤ s.size at hs
  have hd := ResidualLabel.input_length_le s arity ⟨r.signatureLabel h v,d⟩
  change (Holant.Algebraic.frame (encodeNat (r.vertices.get v).1) ++ descriptorWord r v d).length ≤
    ResidualLabel.inputBound s arity at hd
  simp only [List.length_append,Holant.Algebraic.frame_length] at hd
  have hl := treeLabelEncoding_length_le s b arity (label r h v d)
  unfold ticks
  cases framed <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem primitive_bound (framed : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (d : ResidualLabel.Descriptor (arity (r.vertices.get v).1)) (output : List Bool) :
    FixedFieldMachines.primitiveCost (machine s b arity framed) (ticks framed r h v d)
      (some (cfg (sourceLabel s arity (.inr 0)) () (work (RawClosedNetwork.encoding.encode r)
        (List.replicate v.val true) (descriptorWord r v d) [] [] [] output))) ≤
      (12 * ((RawClosedNetwork.encoding.encode r).length + 1) + 2 * ResidualLabel.inputBound s arity +
        2 * s.size + 2 * lengthBound s b arity + 11) * (machine s b arity framed).primitiveBudget :=
  le_trans (FixedFieldMachines.primitiveCost_le _ _ _) (Nat.mul_le_mul_right _ (ticks_le framed r h v d))

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualVertex
