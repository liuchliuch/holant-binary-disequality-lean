import Holant.Certificates.RainbowOrbit.Physical

/-! A single A.18 generator is already an ordinary two-vertex native-X graph.
All other original ports remain external in their original positions. -/
namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def singlePhysicalArity : Fin 2 → ℕ := Fin.cases 4 (fun _ => 2)

def singlePhysicalPortMap (j : Fin 4) :
    (Σ v : Fin 2, Fin (singlePhysicalArity v)) → (Fin 4 ⊕ (Fin 1 × Bool)) := fun p =>
  Fin.cases (fun k => if k = j then .inr (0,false) else .inl k)
    (fun _ => fun i : Fin 2 => if i = 0 then .inr (0,true) else .inl j) p.1 p.2

def singlePhysicalPortInv (j : Fin 4) :
    (Fin 4 ⊕ (Fin 1 × Bool)) → (Σ v : Fin 2, Fin (singlePhysicalArity v))
  | .inl k => if k = j then ⟨1,(1 : Fin 2)⟩ else ⟨0,k⟩
  | .inr (_,false) => ⟨0,j⟩
  | .inr (_,true) => ⟨1,(0 : Fin 2)⟩

def singlePhysicalShape (j : Fin 4) : NetworkShape 4 where
  vertices := 2
  arity := singlePhysicalArity
  edges := 1
  ports := {
    toFun := singlePhysicalPortMap j
    invFun := singlePhysicalPortInv j
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases j <;> fin_cases v <;> dsimp [singlePhysicalArity] at i <;>
        fin_cases i <;> rfl
    right_inv q := by
      cases q with
      | inl k => fin_cases j <;> fin_cases k <;> rfl
      | inr q => rcases q with ⟨e,b⟩; fin_cases j <;> fin_cases e <;> cases b <;> rfl }

def singlePhysicalLabels (F : FourTensor) (M : BinaryMatrix) :
    (v : Fin 2) → Signature ℂ (singlePhysicalArity v) :=
  Fin.cases F (fun _ => physicalBinarySignature (physicalSource M))

def singlePhysicalNetwork (F : FourTensor) (j : Fin 4) (M : BinaryMatrix) : Network ℂ 4 where
  shape := singlePhysicalShape j
  vertex := singlePhysicalLabels F M
  edge := fun _ => Signature.disequality

def singlePhysicalChoices : (Fin 1 → Bool) ≃ Bool where
  toFun c := !(c 0)
  invFun a _ := !a
  left_inv c := by funext i; fin_cases i; simp
  right_inv a := by simp

theorem singlePhysical_ancestor_assignment (j : Fin 4) (x : Fin 4 → Bool) (a : Bool) :
    (singlePhysicalShape j).assignment x
      (Network.endpointChoiceAssignment (singlePhysicalChoices.symm a)) (0 : Fin 2) =
      Function.update x j a := by
  funext k
  by_cases h : k = j
  · subst k
    simp [singlePhysicalShape,NetworkShape.assignment,singlePhysicalPortMap,
      Network.endpointChoiceAssignment,singlePhysicalChoices]
  · simp [singlePhysicalShape,NetworkShape.assignment,singlePhysicalPortMap,
      singlePhysicalChoices,h]

theorem singlePhysical_product (F : FourTensor) (j : Fin 4) (M : BinaryMatrix)
    (x : Fin 4 → Bool) (a : Bool) :
    (∏ v : Fin 2, singlePhysicalLabels F M v
      ((singlePhysicalShape j).assignment x
        (Network.endpointChoiceAssignment (singlePhysicalChoices.symm a)) v)) =
      F (Function.update x j a) * M (x j) a := by
  simp only [Fin.prod_univ_succ]
  change F ((singlePhysicalShape j).assignment x
    (Network.endpointChoiceAssignment (singlePhysicalChoices.symm a)) (0 : Fin 2)) *
      (physicalSource M (!a) (x j) * 1) = _
  rw [singlePhysical_ancestor_assignment,physicalSource_edge,mul_one]

theorem physical_update_order (x : Fin 4 → Bool) (j : Fin 4) (a : Bool) :
    Function.update x j a = ![if 0 = j then a else x 0,if 1 = j then a else x 1,
      if 2 = j then a else x 2,if 3 = j then a else x 3] := by
  funext k
  fin_cases k <;> simp [Function.update_apply]

theorem act_singlePhysicalLeg (F : FourTensor) (j : Fin 4) (M : BinaryMatrix)
    (x : Fin 4 → Bool) :
    act (physicalSingleLeg j M) F x =
      ∑ a : Bool, M (x j) a * F (Function.update x j a) := by
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext k; fin_cases k <;> rfl
  rw [hx]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  fin_cases j <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp [act,physicalSingleLeg,Signature.coordinateAction,TetrahedralOrientation.sum_four,
      Fin.prod_univ_succ,Matrix.one_apply,physical_update_order]

/-- Exact ordinary native-X realization of one displayed local generator. -/
theorem singlePhysicalNetwork_denote (F : FourTensor) (j : Fin 4) (M : BinaryMatrix) :
    (singlePhysicalNetwork F j M).denote = act (physicalSingleLeg j M) F := by
  rw [singlePhysicalNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 1 → Bool, ∏ v : Fin 2, singlePhysicalLabels F M v
    ((singlePhysicalShape j).assignment x (Network.endpointChoiceAssignment c) v)) = _
  rw [← singlePhysicalChoices.symm.sum_comp]
  simp_rw [singlePhysical_product,act_singlePhysicalLeg]
  simp only [mul_comm]

/-- The single binary's endpoint 0 is internal. -/
@[simp] theorem singlePhysical_internal_port (j : Fin 4) :
    (singlePhysicalShape j).ports ⟨(1 : Fin 2),(0 : Fin 2)⟩ =
      .inr ((0 : Fin 1),true) := rfl

/-- The single binary's endpoint 1 keeps the selected external port number. -/
@[simp] theorem singlePhysical_external_port (j : Fin 4) :
    (singlePhysicalShape j).ports ⟨(1 : Fin 2),(1 : Fin 2)⟩ = .inl j := rfl

theorem singlePhysical_original_other_port (j k : Fin 4) (h : k ≠ j) :
    (singlePhysicalShape j).ports ⟨(0 : Fin 2),k⟩ = .inl k := by
  simp [singlePhysicalShape,singlePhysicalPortMap,h]

theorem singlePhysical_realizes_of_mem (S : SignatureFamily ℂ) (F : FourTensor)
    (j : Fin 4) (M : BinaryMatrix) (hF : (⟨4,F⟩ : AnySignature ℂ) ∈ S)
    (hM : (⟨2,physicalBinarySignature (physicalSource M)⟩ : AnySignature ℂ) ∈ S) :
    Gadget.Realizes S .disequality (act (physicalSingleLeg j M) F) := by
  have h := Gadget.realizes_network (singlePhysicalNetwork F j M) S .disequality
    (by intro v; fin_cases v; exact hF; exact hM)
    (by intro e; rfl)
  rwa [singlePhysicalNetwork_denote] at h

theorem singlePhysical_realizes_of_source_mem (F : FourTensor) (G : Set BinaryMatrix)
    (j : Fin 4) (M : BinaryMatrix) (hM : physicalSource M ∈ G) :
    Gadget.Realizes (physicalFamily F G) .disequality (act (physicalSingleLeg j M) F) := by
  apply singlePhysical_realizes_of_mem
  · exact Or.inl rfl
  · exact Or.inr ⟨physicalSource M,hM,rfl⟩

theorem act_singlePhysicalLeg_smul (F : FourTensor) (j : Fin 4)
    (M : BinaryMatrix) (c : ℂ) :
    act (physicalSingleLeg j (c • M)) F = c • act (physicalSingleLeg j M) F := by
  funext x
  simp only [act_singlePhysicalLeg,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem singlePhysicalNetwork_denote_rescale (F : FourTensor) (j : Fin 4)
    (M : BinaryMatrix) (c : ℂ) :
    (singlePhysicalNetwork F j (c • M)).denote =
      c • (singlePhysicalNetwork F j M).denote := by
  simp only [singlePhysicalNetwork_denote,act_singlePhysicalLeg_smul]

/-- The simultaneous graph equals the fixed word of four actual single-vertex
attachments, in original port order. -/
theorem physicalNetwork_denote_single_word (F : FourTensor) (L : Legs) :
    (physicalNetwork F L).denote =
      (singlePhysicalNetwork
        (singlePhysicalNetwork
          (singlePhysicalNetwork
            (singlePhysicalNetwork F 0 (L 0)).denote 1 (L 1)).denote 2 (L 2)).denote
          3 (L 3)).denote := by
  simp only [singlePhysicalNetwork_denote,act_four_leg_word,physicalNetwork_denote_act]

@[simp] theorem singlePhysicalNetwork_vertices (F : FourTensor) (j : Fin 4)
    (M : BinaryMatrix) : (singlePhysicalNetwork F j M).shape.vertices = 2 := rfl

@[simp] theorem singlePhysicalNetwork_edges (F : FourTensor) (j : Fin 4)
    (M : BinaryMatrix) : (singlePhysicalNetwork F j M).shape.edges = 1 := rfl

end
end Holant.Certificates.RainbowOrbit
