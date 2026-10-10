import Holant.Complexity.UniversalPairReduction.BinaryFamily
import Holant.Complexity.UniversalPairReduction.QuerySemantics
import Holant.Complexity.UniversalPairReduction.DeleteVertex

namespace Holant.Complexity.UniversalPairReduction.BinaryFamily
open Surgery
noncomputable section
variable {K : Type} [CommSemiring K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val))
private theorem cast_signature_heq {m n : ℕ} (hm : m=n) (f : Signature K m) :
    HEq (fun x : Fin n → Bool => f (fun i => x (Fin.cast hm i))) f := by
  subst n
  rfl

 theorem signatures_old_heq (B : BinaryTable K) (i : ℕ) (hi : i<s) :
    HEq (signatures G B ⟨i,Nat.lt_trans hi (Nat.lt_succ_self s)⟩) (G ⟨i,hi⟩) := by
  unfold signatures
  simp only [Fin.val_mk,dif_pos hi]
  exact cast_signature_heq _ _

 def family : SignatureFamily K := Set.range (fun i : Fin s => (⟨arity i.val,G i⟩ : AnySignature K))


variable (r : Input s arity) (v : Fin r.val.vertices.length) (hv : (r.val.vertices.get v).1=s)
include hv

 theorem marked_arity (B : BinaryTable K) : (network G B r).shape.arity v=2 := by
  change extendedArity s arity (r.val.vertices.get v).1=2
  rw [hv]
  simp [extendedArity]

 def hole : BinaryTable K := binaryRaw (network G BinaryTable.delta r) v (marked_arity G r v hv BinaryTable.delta)

 theorem delta_value : value G BinaryTable.delta r=hole G r v hv false true :=
  denote_delta (network G BinaryTable.delta r) v (marked_arity G r v hv BinaryTable.delta)
    (vertex_new G BinaryTable.delta r v hv)

 theorem insert_value (B : BinaryTable K) : value G B r=(hole G r v hv).insert B := by
  have hh := denote_binary_relabel (r.val.shape r.property.1)
    (network G BinaryTable.delta r).vertex (network G B r).vertex
    (fun _ => Signature.disequality) v (marked_arity G r v hv BinaryTable.delta)
    (vertex_old_eq G BinaryTable.delta B r v hv)
  change value G B r=(hole G r v hv).insert _ at hh
  refine hh.trans ?_
  apply congrArg (BinaryTable.insert (hole G r v hv))
  funext a b
  exact vertex_new G B r v hv a b

 theorem native_value : value G Signature.disequality r=(hole G r v hv).close := by
  rw [insert_value,BinaryTable.insert_disequality]

 theorem other_uses (u : Fin r.val.vertices.length) (hne : u≠v) :
    (⟨(network G BinaryTable.delta r).shape.arity u,(network G BinaryTable.delta r).vertex u⟩ : AnySignature K)
      ∈family G := by
  have hu := other_label r v hv u hne
  refine ⟨⟨(r.val.vertices.get u).1,hu⟩,?_⟩
  apply Sigma.ext
  · exact (if_pos hu).symm
  · exact (signatures_old_heq G BinaryTable.delta _ hu).symm

 theorem symmetric_hole
    (hs : ∀f : Signature K 2,Gadget.Realizes (family G) .disequality f → f ![false,true]=f ![true,false]) :
    (hole G r v hv).Symmetric :=
  DeleteVertex.raw_symmetric (network G BinaryTable.delta r) v (marked_arity G r v hv BinaryTable.delta)
    (family G) (other_uses G r v hv) (fun _ => rfl) hs

end
end Holant.Complexity.UniversalPairReduction.BinaryFamily
