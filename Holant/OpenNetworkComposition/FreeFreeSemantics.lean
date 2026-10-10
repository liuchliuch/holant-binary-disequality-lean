import Holant.OpenNetworkComposition.FreeFreeRaw

/-! Exact boundary-corrected tensor law for the explicit disjoint free/free
splice. This contracts different components only, retaining all scalar factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition.FreeFree
variable {K VL FL EL VR FR ER : Type*} {n : ℕ}

variable (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2)
    (fL : FL) (fR : FR) (i : Fin n)
    (hL : L.shape.boundary i=.inr fL) (hR : R.shape.boundary 1=.inr fR)

private def portFlip {V F : Type*} {arity : V → ℕ} (p : Ports V F arity) (a : Bool) : Bool :=
  match p with
  | .inl _ => a
  | .inr _ => !a

private theorem boundaryFlip_eq_portFlip {V F E : Type*} {m : ℕ}
    (N : FiniteNetwork K V F E m) (x : Fin m → Bool) (j : Fin m) :
    N.boundaryFlip x j=portFlip (N.shape.boundary j) (x j) := by
  cases hp : N.shape.boundary j <;> simp [FiniteNetwork.boundaryFlip,portFlip,hp]

private theorem portFlip_cut_left (p : L.shape.CutPorts fL) (a : Bool) :
    portFlip ((portSum L.shape.arity R.shape.arity).symm (.inl p) :
      Ports (VL ⊕ VR) (FiniteShape.CutFree fL ⊕ FiniteShape.CutFree fR)
        (SumArity L.shape.arity R.shape.arity)) a = portFlip (L.shape.cutEmbed fL p) a := by
  cases p <;> rfl

private theorem portFlip_cut_right (p : R.shape.CutPorts fR) (a : Bool) :
    portFlip ((portSum L.shape.arity R.shape.arity).symm (.inr p) :
      Ports (VL ⊕ VR) (FiniteShape.CutFree fL ⊕ FiniteShape.CutFree fR)
        (SumArity L.shape.arity R.shape.arity)) a = portFlip (R.shape.cutEmbed fR p) a := by
  cases p <;> rfl

/-- Boundary correction at each untouched left slot keeps its original type. -/
theorem boundaryFlip_network_away (x : Fin n → Bool) (j : Fin n) (hj : j≠i) :
    (network L R fL fR i hL hR).boundaryFlip x j=L.boundaryFlip x j := by
  rw [boundaryFlip_eq_portFlip,boundaryFlip_eq_portFlip]
  change portFlip ((portSum L.shape.arity R.shape.arity).symm
      (boundary L.shape R.shape fL fR i hL hR j)) (x j) =
    portFlip (L.shape.boundary j) (x j)
  rw [boundary_away L.shape R.shape fL fR i hL hR j hj,
    portFlip_cut_left,L.shape.cutEmbed_cutBoundary]

/-- The replacement boundary slot carries the original right slot-0 correction. -/
theorem boundaryFlip_network_at (x : Fin n → Bool) (b : Bool) :
    (network L R fL fR i hL hR).boundaryFlip x i=R.boundaryFlip (![x i,b]) 0 := by
  rw [boundaryFlip_eq_portFlip,boundaryFlip_eq_portFlip]
  change portFlip ((portSum L.shape.arity R.shape.arity).symm
      (boundary L.shape R.shape fL fR i hL hR i)) (x i) =
    portFlip (R.shape.boundary 0) (x i)
  rw [boundary_at,portFlip_cut_right,R.shape.cutEmbed_cutBoundary]

theorem boundaryFlip_left_update (x : Fin n → Bool) (a : Bool) :
    L.boundaryFlip (Function.update x i a)=
      Function.update ((network L R fL fR i hL hR).boundaryFlip x) i (!a) := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [FiniteNetwork.boundaryFlip,hL]
  · rw [Function.update_of_ne hj,boundaryFlip_network_away L R fL fR i hL hR x j hj]
    cases hp : L.shape.boundary j <;> simp [FiniteNetwork.boundaryFlip,hp,Function.update_of_ne hj]

theorem boundaryFlip_right_binary (x : Fin n → Bool) (b : Bool) :
    R.boundaryFlip (![x i,b]) = ![((network L R fL fR i hL hR).boundaryFlip x) i,!b] := by
  funext j
  fin_cases j
  · exact (boundaryFlip_network_at L R fL fR i hL hR x b).symm
  · simp [FiniteNetwork.boundaryFlip,hR]

variable [Fintype VL] [Fintype FL] [Fintype EL]
    [Fintype VR] [Fintype FR] [Fintype ER] [CommSemiring K]

/-- Exact ordered tensor contraction for two disjoint gadgets joined at free
boundary slots. The exposed result slot is R's original slot 0. -/
theorem network_tensor
    (eL : ∀ e,L.edge e=.disequality) (eR : ∀ e,R.edge e=.disequality)
    (x : Fin n → Bool) :
    (network L R fL fR i hL hR).tensor x =
      ∑ a : Bool,∑ b : Bool,L.tensor (Function.update x i a) * R.tensor (![x i,b]) *
        Signature.disequality a b := by
  rw [FiniteNetwork.tensor_eq_raw_boundaryFlip _ (network_edges_native L R fL fR i hL hR eL eR)]
  rw [network_raw L R fL fR i hL hR (eL _) (eR _)]
  simp_rw [L.tensor_eq_raw_boundaryFlip eL,R.tensor_eq_raw_boundaryFlip eR,
    boundaryFlip_left_update L R fL fR i hL hR,boundaryFlip_right_binary L R fL fR i hL hR]
  simp only [Fintype.sum_bool]
  simp [Signature.disequality]
  exact add_comm _ _

/-- The same exact law for the repository's original OpenNetwork.tensor. -/
theorem toOpen_network_tensor
    (eL : ∀ e,L.edge e=.disequality) (eR : ∀ e,R.edge e=.disequality)
    (x : Fin n → Bool) :
    (network L R fL fR i hL hR).toOpen.tensor x =
      ∑ a : Bool,∑ b : Bool,L.tensor (Function.update x i a) * R.tensor (![x i,b]) *
        Signature.disequality a b := by
  rw [FiniteNetwork.tensor_toOpen,network_tensor L R fL fR i hL hR eL eR]

include fL fR hL hR

/-- Sufficient disjoint free/free closure with exact native-edge provenance and
no additional signature vertices or scalar normalization. -/
theorem realizes_splice
    (family : SignatureFamily K)
    (vL : ∀ v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K) ∈ family)
    (vR : ∀ v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K) ∈ family)
    (eL : ∀ e,L.edge e=.disequality) (eR : ∀ e,R.edge e=.disequality) :
    Gadget.Realizes family .disequality
      (fun x => ∑ a : Bool,∑ b : Bool,L.tensor (Function.update x i a) * R.tensor (![x i,b]) *
        Signature.disequality a b) := by
  have ht : (network L R fL fR i hL hR).tensor =
      (fun x => ∑ a : Bool,∑ b : Bool,L.tensor (Function.update x i a) * R.tensor (![x i,b]) *
        Signature.disequality a b) := funext (network_tensor L R fL fR i hL hR eL eR)
  rw [← ht]
  exact realizes_network L R fL fR i hL hR family vL vR eL eR

end Holant.OpenNetworkComposition.FreeFree
