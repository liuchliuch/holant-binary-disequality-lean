import Holant.Certificates.RainbowOrbit.Action
import Holant.NativeNetwork
import Holant.NetworkAsGadget

/-! The actual local dressings of A.18, with all four binary vertices visible.
The original port `j` meets endpoint 0 of `X * (L j).transpose` through one
native-X edge; endpoint 1 is external port `j`. Thus no coefficient-space
similarity is used as a physical operation. -/
namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def physicalX : BinaryMatrix := Signature.disequality

/-- Actual source binary, in internal-first and external-second order. -/
def physicalSource (L : BinaryMatrix) : BinaryMatrix := physicalX * L.transpose

def physicalBinarySignature (B : BinaryMatrix) : Signature ℂ 2 :=
  fun x => B (x 0) (x 1)

theorem physicalSource_apply (L : BinaryMatrix) (a b : Bool) :
    physicalSource L a b = L b (!a) := by
  cases a <;> cases b <;>
    simp [physicalSource,physicalX,Matrix.mul_apply,Signature.disequality]

@[simp] theorem physicalSource_edge (L : BinaryMatrix) (a b : Bool) :
    physicalSource L (!b) a = L a b := by
  rw [physicalSource_apply]
  simp

/-- The transpose is forced by the displayed order of the binary's ports. -/
theorem physicalSource_effective (L : BinaryMatrix) :
    (physicalSource L).transpose * physicalX = L := by
  ext a b
  cases a <;> cases b <;>
    simp [physicalSource_apply,physicalX,Matrix.mul_apply,Signature.disequality]

theorem physicalSource_smul (c : ℂ) (L : BinaryMatrix) :
    physicalSource (c • L) = c • physicalSource L := by
  ext a b
  simp [physicalSource_apply]

def physicalArity : Fin 5 → ℕ := Fin.cases 4 (fun _ => 2)

def physicalPortMap : (Σ v : Fin 5, Fin (physicalArity v)) →
    (Fin 4 ⊕ (Fin 4 × Bool)) := fun p =>
  Fin.cases (fun i => .inr (i,false))
    (fun j => fun i : Fin 2 => if i = 0 then .inr (j,true) else .inl j) p.1 p.2

def physicalPortInv : (Fin 4 ⊕ (Fin 4 × Bool)) →
    (Σ v : Fin 5, Fin (physicalArity v))
  | .inl j => ⟨j.succ,(1 : Fin 2)⟩
  | .inr (j,false) => ⟨0,j⟩
  | .inr (j,true) => ⟨j.succ,(0 : Fin 2)⟩

def physicalShape : NetworkShape 4 where
  vertices := 5
  arity := physicalArity
  edges := 4
  ports := {
    toFun := physicalPortMap
    invFun := physicalPortInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [physicalArity] at i <;> fin_cases i <;> rfl
    right_inv q := by
      cases q with
      | inl j => fin_cases j <;> rfl
      | inr q => rcases q with ⟨j,b⟩; fin_cases j <;> cases b <;> rfl }

/-- The original ordered port `j` is the false endpoint of native edge `j`. -/
@[simp] theorem physical_original_port (j : Fin 4) :
    physicalShape.ports ⟨(0 : Fin 5),j⟩ = .inr (j,false) := rfl

/-- Port 0 of the actual binary is the internal endpoint of its native edge. -/
@[simp] theorem physical_binary_internal_port (j : Fin 4) :
    physicalShape.ports ⟨j.succ,(0 : Fin 2)⟩ = .inr (j,true) := rfl

/-- Port 1 of the actual binary is the external port, with order unchanged. -/
@[simp] theorem physical_binary_external_port (j : Fin 4) :
    physicalShape.ports ⟨j.succ,(1 : Fin 2)⟩ = .inl j := rfl

def physicalLabels (F : FourTensor) (L : Legs) :
    (v : Fin 5) → Signature ℂ (physicalArity v) :=
  Fin.cases F (fun j => physicalBinarySignature (physicalSource (L j)))

def physicalNetwork (F : FourTensor) (L : Legs) : Network ℂ 4 where
  shape := physicalShape
  vertex := physicalLabels F L
  edge := fun _ => Signature.disequality

def physicalChoices : (Fin 4 → Bool) ≃ (Fin 4 → Bool) where
  toFun c j := !(c j)
  invFun y j := !(y j)
  left_inv c := by funext j; simp
  right_inv y := by funext j; simp

theorem physical_ancestor_assignment (x y : Fin 4 → Bool) :
    physicalShape.assignment x
      (Network.endpointChoiceAssignment (physicalChoices.symm y)) (0 : Fin 5) = y := by
  funext j
  simp [physicalShape,NetworkShape.assignment,physicalPortMap,
    Network.endpointChoiceAssignment,physicalChoices]

theorem physical_binary_assignment (L : Legs) (x y : Fin 4 → Bool) (j : Fin 4) :
    physicalLabels (fun _ => 0) L j.succ
      (physicalShape.assignment x
        (Network.endpointChoiceAssignment (physicalChoices.symm y)) j.succ) =
      L j (x j) (y j) := by
  change physicalSource (L j) (!(y j)) (x j) = _
  exact physicalSource_edge _ _ _

theorem physical_product (F : FourTensor) (L : Legs) (x y : Fin 4 → Bool) :
    (∏ v : Fin 5, physicalLabels F L v
      (physicalShape.assignment x (Network.endpointChoiceAssignment (physicalChoices.symm y)) v)) =
      F y * ∏ j : Fin 4, L j (x j) (y j) := by
  simp only [Fin.prod_univ_succ]
  change F (physicalShape.assignment x
    (Network.endpointChoiceAssignment (physicalChoices.symm y)) (0 : Fin 5)) * _ = _
  rw [physical_ancestor_assignment]
  change F y *
    (physicalSource (L 0) (!(y 0)) (x 0) *
      (physicalSource (L 1) (!(y 1)) (x 1) *
        (physicalSource (L 2) (!(y 2)) (x 2) *
          (physicalSource (L 3) (!(y 3)) (x 3) * 1)))) = _
  simp [physicalSource_edge]

/-- Exact denotation of the five-vertex graph, for an arbitrary four-tensor. -/
theorem physicalNetwork_denote (F : FourTensor) (L : Legs) :
    (physicalNetwork F L).denote = Signature.coordinateAction L F := by
  rw [physicalNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 4 → Bool, ∏ v : Fin 5, physicalLabels F L v
    (physicalShape.assignment x (Network.endpointChoiceAssignment c) v)) = _
  rw [← physicalChoices.symm.sum_comp]
  simp_rw [physical_product]
  simp only [Signature.coordinateAction,mul_comm]

theorem physicalNetwork_denote_act (F : FourTensor) (L : Legs) :
    (physicalNetwork F L).denote = act L F := physicalNetwork_denote F L

/-- Exactly the original tensor and four actual binary source labels occur. -/
def physicalResources (F : FourTensor) (L : Legs) : SignatureFamily ℂ :=
  {p | p = ⟨4,F⟩ ∨ ∃ j : Fin 4,
    p = ⟨2,physicalBinarySignature (physicalSource (L j))⟩}

theorem physical_realizes (F : FourTensor) (L : Legs) :
    Gadget.Realizes (physicalResources F L) .disequality (act L F) := by
  have h := Gadget.realizes_network (physicalNetwork F L) (physicalResources F L) .disequality
    (by intro v; fin_cases v
        · exact Or.inl rfl
        · exact Or.inr ⟨0,rfl⟩
        · exact Or.inr ⟨1,rfl⟩
        · exact Or.inr ⟨2,rfl⟩
        · exact Or.inr ⟨3,rfl⟩)
    (by intro e; rfl)
  rwa [physicalNetwork_denote_act] at h

theorem physical_realizes_of_mem (S : SignatureFamily ℂ) (F : FourTensor) (L : Legs)
    (hF : (⟨4,F⟩ : AnySignature ℂ) ∈ S)
    (hL : ∀ j, (⟨2,physicalBinarySignature (physicalSource (L j))⟩ : AnySignature ℂ) ∈ S) :
    Gadget.Realizes S .disequality (act L F) := by
  apply (physical_realizes F L).mono
  rintro p (rfl | ⟨j,rfl⟩)
  · exact hF
  · exact hL j

/-- Generic actual source family; current marked-group membership can be
substituted here without declaring any coefficient similarity a generator. -/
def physicalFamily (F : FourTensor) (G : Set BinaryMatrix) : SignatureFamily ℂ :=
  {p | p = ⟨4,F⟩ ∨ ∃ B ∈ G, p = ⟨2,physicalBinarySignature B⟩}

theorem physical_realizes_of_source_mem (F : FourTensor) (G : Set BinaryMatrix) (L : Legs)
    (hL : ∀ j, physicalSource (L j) ∈ G) :
    Gadget.Realizes (physicalFamily F G) .disequality (act L F) := by
  apply physical_realizes_of_mem
  · exact Or.inl rfl
  · intro j
    exact Or.inr ⟨physicalSource (L j),hL j,rfl⟩

theorem physicalSource_mem {G : Set BinaryMatrix}
    (hX : physicalX ∈ G) (htranspose : ∀ B ∈ G, B.transpose ∈ G)
    (hmul : ∀ B ∈ G, ∀ C ∈ G, B * C ∈ G) {L : BinaryMatrix} (hL : L ∈ G) :
    physicalSource L ∈ G := hmul _ hX _ (htranspose _ hL)

@[simp] theorem physicalNetwork_vertices (F : FourTensor) (L : Legs) :
    (physicalNetwork F L).shape.vertices = 5 := rfl

@[simp] theorem physicalNetwork_edges (F : FourTensor) (L : Legs) :
    (physicalNetwork F L).shape.edges = 4 := rfl

@[simp] theorem physicalNetwork_binary_vertices (F : FourTensor) (L : Legs) :
    (Finset.univ.filter (fun v => (physicalNetwork F L).shape.arity v = 2)).card = 4 := by
  change (Finset.univ.filter (fun v : Fin 5 => physicalArity v = 2)).card = 4
  decide

@[simp] theorem physicalNetwork_ancestor_vertices (F : FourTensor) (L : Legs) :
    (Finset.univ.filter (fun v => (physicalNetwork F L).shape.arity v = 4)).card = 1 := by
  change (Finset.univ.filter (fun v : Fin 5 => physicalArity v = 4)).card = 1
  decide

@[simp] theorem physicalNetwork_edge_native (F : FourTensor) (L : Legs) (e : Fin 4) :
    (physicalNetwork F L).edge e = Signature.disequality := rfl

/-- Noncanonical source representatives record the product of all four scalars. -/
theorem physicalNetwork_denote_rescale (F : FourTensor) (L : Legs) (c : Fin 4 → ℂ) :
    (physicalNetwork F (fun j => c j • L j)).denote =
      (∏ j, c j) • (physicalNetwork F L).denote := by
  simp only [physicalNetwork_denote_act,act_rescale_legs]

theorem physical_representative_scalar_ne_zero (c : Fin 4 → ℂ) (hc : ∀ j, c j ≠ 0) :
    (∏ j, c j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)

/-- One literal local operation on the indicated ordered port. -/
def physicalSingleLeg (j : Fin 4) (M : BinaryMatrix) : Legs :=
  fun k => if k = j then M else 1

/-- The four-tuple action is the fixed word applying ports 0,1,2,3 in order. -/
theorem act_four_leg_word (F : FourTensor) (L : Legs) :
    act (physicalSingleLeg 3 (L 3))
      (act (physicalSingleLeg 2 (L 2))
        (act (physicalSingleLeg 1 (L 1))
          (act (physicalSingleLeg 0 (L 0)) F))) = act L F := by
  rw [act_comp,act_comp,act_comp]
  congr 1
  funext j
  fin_cases j <;> simp [physicalSingleLeg]

end
end Holant.Certificates.RainbowOrbit
