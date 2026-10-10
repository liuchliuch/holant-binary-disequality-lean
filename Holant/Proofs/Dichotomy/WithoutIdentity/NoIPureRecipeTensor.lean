import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeOpenSubstitution
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRecipeFactor

/-! A heterogeneous finite recipe is an actual disjoint native tensor.
Its literal signed ports flatten through a bijection, including nullary rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureRecipeTensor
open Holant Holant.Complexity
open scoped BigOperators
namespace R
export NoIPurePhaseRecipeFactor (Port word incidence total)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {s k m : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))
variable {ns : Fin k → ℕ}
variable (N : (v : Fin k) → NativeAntiTargetSource.Output H (ns v))
abbrev Positions := Σ v : Fin k, Fin (ns v)
abbrev size := Fintype.card (Positions (ns:=ns))

def finite : FiniteNetwork K (Fin k) Empty (size (ns:=ns)) where
  arity := ns
  ports := (Fintype.equivFin (Positions (ns:=ns))).trans
    (Equiv.sumEmpty (Fin (size (ns:=ns))) (Empty × Bool)).symm
  vertex v := (N v).network.denote
  edge := Empty.elim

abbrev outer := (finite H N).toNetwork

def replacement (v : Fin (outer H N).shape.vertices) :
    NativeAntiTargetSource.Output H ((outer H N).shape.arity v) :=
  N ((Fintype.equivFin (Fin k)).symm v)

def output : NativeAntiTargetSource.Output H (size (ns:=ns)) :=
  NoINativeOpenSubstitution.output H (outer H N) (replacement H N)
    (fun e => Empty.elim ((Fintype.equivFin Empty).symm e))

theorem value (x : Fin (size (ns:=ns)) → Bool) :
    (output H N).network.denote x =
      ∏ v, (N v).network.denote (fun j => x ((Fintype.equivFin (Positions (ns:=ns))) ⟨v,j⟩)) := by
  rw [output,NoINativeOpenSubstitution.value H (outer H N) (replacement H N) _ (fun _ => rfl)]
  rw [outer,FiniteNetwork.denote_toNetwork]
  simp [finite,FiniteNetwork.denote]

def ports (ps : (v : Fin k) → Fin (ns v) → R.Port m) :
    Fin (size (ns:=ns)) → R.Port m := fun j =>
  let i := (Fintype.equivFin (Positions (ns:=ns))).symm j
  ps i.1 i.2

@[simp] theorem ports_apply (ps : (v : Fin k) → Fin (ns v) → R.Port m)
    (v : Fin k) (j : Fin (ns v)) :
    ports ps ((Fintype.equivFin (Positions (ns:=ns))) ⟨v,j⟩) = ps v j := by
  change (fun i : Positions (ns:=ns) => ps i.1 i.2)
    ((Fintype.equivFin (Positions (ns:=ns))).symm
      ((Fintype.equivFin (Positions (ns:=ns))) ⟨v,j⟩)) = _
  rw [Equiv.symm_apply_apply]

theorem word_value (ps : (v : Fin k) → Fin (ns v) → R.Port m) (z : Fin m → Bool) :
    (output H N).network.denote (R.word (ports ps) z) =
      ∏ v, (N v).network.denote (R.word (ps v) z) := by
  rw [value]
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  change (match ports ps ((Fintype.equivFin (Positions (ns:=ns))) ⟨v,j⟩) with
    | .inl b => b | .inr (j,b) => b ^^ z j) = _
  rw [ports_apply]
  rfl

theorem incidence (ps : (v : Fin k) → Fin (ns v) → R.Port m) (j : Fin m) :
    R.incidence (ports ps) j = R.total ps j := by
  unfold R.incidence
  rw [← (Fintype.equivFin (Positions (ns:=ns))).sum_comp]
  simp only [Fintype.sum_sigma,ports_apply]
  rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureRecipeTensor
end
