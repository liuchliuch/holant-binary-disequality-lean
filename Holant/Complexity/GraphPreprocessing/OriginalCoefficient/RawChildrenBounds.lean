import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

theorem prepared_length (x : Input s b arity) :
    (ChildEnumerate.inputEncoding.encode (prepared x)).length≤20*((RawClosedNetwork.encoding.encode x.1.val).length+1)^2+3 := by
  have he := RawEdgeTable.output_length x.1
  have hp := RawParentTable.output_length x.1
  have hn := x.1.val.counts_le_encoded_length
  have ht := x.2.isLt
  change (Holant.Algebraic.frame (List.replicate x.1.val.vertices.length true)++
    ReachRound.encode (ReachRound.graphEdges (x.1.val.graph x.1.property))).length≤_ at he
  change (ParentRowEncoding.table.encode (x.1.val.graph x.1.property).parentTable).length≤_ at hp
  change (Holant.Algebraic.frame (ReachRound.encode (ReachRound.graphEdges (x.1.val.graph x.1.property)))++
    (Holant.Algebraic.frame (List.replicate x.2.val true)++ParentRowEncoding.table.encode (x.1.val.graph x.1.property).parentTable)).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,List.length_replicate] at he ⊢
  nlinarith

theorem output_length (x : Input s b arity) :
    (ChildEnumerate.outputEncoding.encode (value x)).length≤2*((RawClosedNetwork.encoding.encode x.1.val).length+1)^2+1 := by
  have hv := x.1.val.counts_le_encoded_length
  have hb := ChildEnumerate.children_bits_length (ReachRound.graphEdges (x.1.val.graph x.1.property)) x.2.val 0
    (x.1.val.graph x.1.property).parentTable
  rw [(x.1.val.graph x.1.property).parentTable_length] at hb
  change (ChildEnumerate.bits (ChildEnumerate.value (prepared x))).length≤
    x.1.val.vertices.length*(2*(0+x.1.val.vertices.length)+2) at hb
  have hi : x.1.val.vertices.length≤(RawClosedNetwork.encoding.encode x.1.val).length := by omega
  have hm := Nat.mul_le_mul hi (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hi) 2)
  have he : value x=ChildEnumerate.value (prepared x) := (ChildEnumerate.original_value (x.1.val.graph x.1.property) x.2).symm
  rw [he]
  change (framedListEncode UnaryBinary.unaryEncoding (ChildEnumerate.value (prepared x))).length≤_
  rw [←ChildEnumerate.bits_encode,List.length_append,List.length_singleton]
  nlinarith
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawChildren
