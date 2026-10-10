import Holant.Dihedral.CompatibleClosure.NativeCard

/-! Changing which original q ports are connected changes incidence only;
the q vertex label, actual binary representative and residual order are retained. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Tractable
set_option backward.isDefEq.respectTransparency false

private def rewire {V E : Type*} {n : ℕ} (N : FiniteNetwork Scalar V E n)
    (p : (v : V) → Equiv.Perm (Fin (N.arity v))) : FiniteNetwork Scalar V E n where
  arity := N.arity
  ports := (Equiv.sigmaCongrRight p).trans N.ports
  vertex := N.vertex
  edge := N.edge

private theorem rewire_denote {V E : Type*} [Fintype V] [Fintype E] {n : ℕ}
    (N : FiniteNetwork Scalar V E n) (p : (v : V) → Equiv.Perm (Fin (N.arity v))) :
    (rewire N p).denote =
      ({ N with vertex := fun v => Tensor.reindex (p v) (N.vertex v) } : FiniteNetwork Scalar V E n).denote := by
  rfl

private def localOrder {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat)
    (order : Equiv.Perm (Fin (n+2))) : (v : Bool) → Equiv.Perm (Fin ((nativeCardFinite q C).arity v))
  | false => order.symm
  | true => Equiv.refl _

def nativeCardAtFinite {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat)
    (order : Equiv.Perm (Fin (n+2))) : FiniteNetwork Scalar Bool Bool n :=
  rewire (nativeCardFinite q C) (localOrder q C order)

def nativeCardAt {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat)
    (order : Equiv.Perm (Fin (n+2))) : Network Scalar n := (nativeCardAtFinite q C order).toNetwork

theorem nativeCardAt_denote {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat)
    (order : Equiv.Perm (Fin (n+2))) :
    (nativeCardAt q C order).denote = nativeCardValue (Tensor.reindex order.symm q) C := by
  rw [nativeCardAt,FiniteNetwork.denote_toNetwork,nativeCardAtFinite,rewire_denote]
  have he : ({ nativeCardFinite q C with
        vertex := fun v => Tensor.reindex (localOrder q C order v) ((nativeCardFinite q C).vertex v) } :
        FiniteNetwork Scalar Bool Bool n) = nativeCardFinite (Tensor.reindex order.symm q) C := by
    have hv : (fun v => Tensor.reindex (localOrder q C order v) ((nativeCardFinite q C).vertex v)) =
        (nativeCardFinite (Tensor.reindex order.symm q) C).vertex := by
      funext v
      cases v <;> rfl
    exact congrArg (fun f => ({ nativeCardFinite q C with vertex := f } : FiniteNetwork Scalar Bool Bool n)) hv
  rw [he,← FiniteNetwork.denote_toNetwork]
  exact nativeCard_denote _ _

/-- The original q and C resources are unchanged under arbitrary original-port
choice; only their incidence map is rewired. -/
theorem nativeCardAt_realizes {n : ℕ} (F : SignatureFamily Scalar)
    (q : Signature Scalar (n+2)) (C : Mat) (order : Equiv.Perm (Fin (n+2)))
    (hq : (⟨n+2,q⟩ : AnySignature Scalar) ∈ F)
    (hc : (⟨2,kernelSignature C⟩ : AnySignature Scalar) ∈ F) :
    Gadget.Realizes F .disequality (nativeCardValue (Tensor.reindex order.symm q) C) := by
  have hh := Gadget.realizes_network (nativeCardAt q C order) F .disequality
    (by
      intro v
      change (⟨(nativeCardFinite q C).arity ((Fintype.equivFin Bool).symm v),
        (nativeCardFinite q C).vertex ((Fintype.equivFin Bool).symm v)⟩ : AnySignature Scalar) ∈ F
      cases h : (Fintype.equivFin Bool).symm v
      · exact hq
      · exact hc)
    (by intro e; rfl)
  rwa [nativeCardAt_denote] at hh

/-- Every exposed port refers to its original q occurrence, in the requested
order after the two chosen endpoints. -/
theorem nativeCardAt_boundary {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat)
    (order : Equiv.Perm (Fin (n+2))) (i : Fin n) :
    (nativeCardAtFinite q C order).ports.symm (.inl i) = ⟨false,order i.succ.succ⟩ := by
  change (Equiv.sigmaCongrRight (localOrder q C order)).symm
    ((nativeCardFinite q C).ports.symm (.inl i)) = _
  rfl

theorem nativeCardAt_original_ends {n : ℕ} (q : Signature Scalar (n+2)) (C : Mat)
    (order : Equiv.Perm (Fin (n+2))) :
    (nativeCardAtFinite q C order).ports.symm (.inr (false,false)) = ⟨false,order 0⟩ ∧
    (nativeCardAtFinite q C order).ports.symm (.inr (true,false)) = ⟨false,order 1⟩ := by
  constructor <;> rfl

end Holant.Dihedral.CompatibleClosure
