import Holant.OpenNetworkComposition.FreeFree

/-! Native disequality boundary correction and exact local free-end elimination.
These identities use the existing finite presentation of OpenNetwork.tensor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace FiniteNetwork
variable {K V F E : Type*} {n : ℕ}

/-- Complement precisely the exposed free coordinates, leaving ordinary ones. -/
def boundaryFlip (N : FiniteNetwork K V F E n) (x : Fin n → Bool) (j : Fin n) : Bool :=
  match N.shape.boundary j with
  | .inl _ => x j
  | .inr _ => !(x j)

@[simp] theorem boundaryFlip_involutive (N : FiniteNetwork K V F E n) (x : Fin n → Bool) :
    N.boundaryFlip (N.boundaryFlip x)=x := by
  funext j
  cases h : N.shape.boundary j <;> simp [boundaryFlip,h]

variable [CommSemiring K]

theorem boundaryKernel_eq_equality_flip (N : FiniteNetwork K V F E n)
    (he : ∀ e,N.edge e=.disequality) (x : Fin n → Bool) (j : Fin n) (b : Bool) :
    N.boundaryKernel j (x j) b = Signature.equality (N.boundaryFlip x j) b := by
  cases h : N.shape.boundary j with
  | inl p => simp [boundaryKernel,boundaryFlip,h]
  | inr f =>
    simp only [boundaryKernel,h,he,EdgeKind.value,boundaryFlip]
    cases hx : x j <;> cases b <;> rfl

variable [Fintype V] [Fintype F] [Fintype E]

/-- Exact boundary correction under the native-X hypothesis, without a new
semantic model or any assumption about closure under contraction. -/
theorem tensor_eq_raw_boundaryFlip (N : FiniteNetwork K V F E n)
    (he : ∀ e,N.edge e=.disequality) (x : Fin n → Bool) :
    N.tensor x=N.raw (N.boundaryFlip x) := by
  classical
  simp only [tensor,Signature.coordinateAction,N.boundaryKernel_eq_equality_flip he,
    Signature.prod_equality]
  simp

theorem tensor_eq_sum_boundaryFlip (N : FiniteNetwork K V F E n)
    (he : ∀ e,N.edge e=.disequality) (x : Fin n → Bool) :
    N.tensor x = ∑ z : Ports V F N.shape.arity → Bool,
      if ∀ j,z (N.shape.boundary j)=N.boundaryFlip x j then N.weight z else 0 := by
  classical
  rw [N.tensor_eq_raw_boundaryFlip he]
  rfl

end FiniteNetwork
namespace FiniteShape
variable {V F E : Type*} {n : ℕ}

/-- Restore an assignment at the deleted stub, keeping every surviving port. -/
def restoreAssignment (s : FiniteShape V F E n) (f : F) (z : s.CutPorts f → Bool)
    (a : Bool) (p : Ports V F s.arity) : Bool := by
  classical
  exact if h : p=.inr f then a else z (s.cutPort f p h)

@[simp] theorem restoreAssignment_deleted (s : FiniteShape V F E n) (f : F)
    (z : s.CutPorts f → Bool) (a : Bool) : s.restoreAssignment f z a (.inr f)=a := by
  simp [restoreAssignment]

@[simp] theorem restoreAssignment_retained (s : FiniteShape V F E n) (f : F)
    (z : s.CutPorts f → Bool) (a : Bool) (p : s.CutPorts f) :
    s.restoreAssignment f z a (s.cutEmbed f p)=z p := by
  classical
  rw [restoreAssignment,dite_eq_right (s.cutEmbed_ne f p)]
  apply congrArg z
  apply (s.cutEmbed f).injective
  simp

/-- The assignment bijection isolates exactly the deleted free bit. -/
def cutAssignmentEquiv (s : FiniteShape V F E n) (f : F) :
    (Ports V F s.arity → Bool) ≃ (Bool × (s.CutPorts f → Bool)) where
  toFun z := (z (.inr f),fun p => z (s.cutEmbed f p))
  invFun az := s.restoreAssignment f az.2 az.1
  left_inv := by
    intro z
    funext p
    by_cases h : p=.inr f
    · subst p; simp
    · simp [restoreAssignment,h]
  right_inv := by
    rintro ⟨a,z⟩
    apply Prod.ext
    · simp
    · funext p; simp

end FiniteShape
namespace FreeFree
variable {K : Type*} [CommSemiring K]

/-- The three native edge factors contract to the single fused edge, preserving
any scalar multiplier in either component. -/
theorem native_three_edge_elimination (cL cR : K) (u v : Bool) :
    (∑ a : Bool,∑ b : Bool,
      (cL * Signature.disequality a u) *
      (cR * Signature.disequality b v) * Signature.disequality a b) =
      cL*cR*Signature.disequality u v := by
  cases u <;> cases v <;> simp [Signature.disequality]

/-- The same local identity after correcting the two selected free boundaries. -/
theorem corrected_native_elimination (cL cR : K) (u v : Bool) :
    (∑ a : Bool,∑ b : Bool,
      (cL * Signature.disequality (!a) u) *
      (cR * Signature.disequality (!b) v) * Signature.disequality a b) =
      cL*cR*Signature.disequality u v := by
  cases u <;> cases v <;> simp [Signature.disequality]

end FreeFree
end Holant.OpenNetworkComposition
