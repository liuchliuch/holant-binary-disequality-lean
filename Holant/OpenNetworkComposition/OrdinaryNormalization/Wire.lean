import Holant.OpenNetworkComposition.OrdinaryTensor
import Holant.OpenNetworkComposition.OfOpen

/-! A genuinely ordinary native-X wire using two literal I vertices.  The
construction keeps the exact X table, with no scalar normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.OrdinaryNormalization
variable {K : Type*} [CommSemiring K]

/-- The literal supplied binary identity, in ordered signature form. -/
def identitySignature : Signature K 2 := fun x => Signature.equality (x 0) (x 1)

/-- A single genuine literal-I vertex has two ordinary boundary occurrences. -/
abbrev identityVertex : FiniteNetwork K (Fin 1) (Fin 0) (Fin 0) 2 :=
  FiniteNetwork.ofOpen (OpenNetwork.singleVertex identitySignature)

@[simp] theorem identityVertex_tensor : (identityVertex (K := K)).tensor=identitySignature := by
  exact (FiniteNetwork.ofOpen_tensor _).trans (OpenNetwork.tensor_vertex _)

theorem identityVertex_native (e : Fin 0) :
    (identityVertex (K := K)).edge e=.disequality := Fin.elim0 e

abbrev WireVertices := Fin 1 ⊕ Fin 1
abbrev WireFree := Fin 0 ⊕ Fin 0
abbrev WireEdges := (Fin 0 ⊕ Fin 0) ⊕ Unit

/-- Two literal I vertices, joined at their second ports by one native X.
Its ordered boundary is the first port of each vertex. -/
abbrev wire : FiniteNetwork K WireVertices WireFree WireEdges 2 :=
  Ordinary.network identityVertex identityVertex 1 ⟨0,(1 : Fin 2)⟩ ⟨0,(1 : Fin 2)⟩ rfl rfl

theorem wire_native (e : WireEdges) : (wire (K := K)).edge e=.disequality :=
  Ordinary.network_edges_native _ _ _ _ _ _ _ identityVertex_native identityVertex_native e

theorem wire_uses (family : SignatureFamily K)
    (hI : (⟨2,identitySignature (K := K)⟩ : AnySignature K)∈family) :
    ∀v,(⟨(wire (K := K)).shape.arity v,(wire (K := K)).vertex v⟩ : AnySignature K)∈family := by
  rintro (v|v) <;> exact hI

/-- The actual boundary-corrected tensor is exactly the native X kernel. -/
theorem wire_tensor : (wire (K := K)).tensor=
    (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  rw [wire,Ordinary.network_tensor _ _ _ _ _ _ _ identityVertex_native identityVertex_native,
    identityVertex_tensor]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [spliceTensor,identitySignature,Signature.equality,
      Signature.disequality,h0,h1]

/-- Attaching the ordinary I-X-I wire through a native X acts identically at
one ordered boundary slot. This is exact even for the zero signature. -/
theorem splice_wire {n : ℕ} (f : Signature K n) (i : Fin n) :
    spliceTensor f (wire (K := K)).tensor i=f := by
  rw [wire_tensor]
  funext x
  have hu : Function.update x i (x i)=x := Function.update_eq_self i x
  cases h : x i <;>
    simp [spliceTensor,Signature.disequality,h] <;>
    simpa only [h] using congrArg f hu

/-- Both external occurrences of the wire are genuine ordinary vertex ports. -/
theorem wire_boundary_ordinary (j : Fin 2) :
    ∃p,(wire (K := K)).shape.boundary j=.inl p := by
  cases h : (wire (K := K)).shape.boundary j with
  | inl p => exact ⟨p,rfl⟩
  | inr f => exact isEmptyElim f

end Holant.OpenNetworkComposition.OrdinaryNormalization
