import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidencePorts

/-! Translation changes actual signed substitutions and their coefficients,
not the coefficient field. It normalizes an odd rank-three incidence kernel
to one common charge on all seven exposed bundles. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceTranslation
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word)
open scoped BigOperators
namespace W
export NoIPurePhaseRecipeFactor (incidence)
export NoIPurePhaseIncidenceWeight (residue)
end W
namespace A
export NoIPurePhaseIncidenceCore.C (codeSeven)
end A
namespace Q
export NoIPurePhaseIncidenceRegularization (translated)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m : ℕ}

def ports (p : Fin n→Port m) (u : Fin m→Bool) (i : Fin n) : Port m :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,s)=>.inr (j,s ^^ u j)

theorem value (p : Fin n→Port m) (u z : Fin m→Bool) :
    word (ports p u) z=word p (fun j=>u j ^^ z j) := by
  funext i
  cases h:p i with
  | inl b=>simp [word,ports,h]
  | inr t=>
    rcases t with ⟨j,s⟩
    simp only [word,ports,h]
    cases s <;> cases u j <;> cases z j <;> rfl

theorem incidence (p : Fin n→Port m) (u : Fin m→Bool) (j : Fin m) :
    W.incidence (ports p u) j=if u j then -(W.incidence p j) else W.incidence p j := by
  unfold W.incidence
  cases hz:u j
  · apply Finset.sum_congr rfl
    intro i _
    cases hp:p i with
    | inl b=>simp [ports,hp]
    | inr t=>
      rcases t with ⟨k,s⟩
      by_cases hk:k=j
      · subst k;simp [ports,hp,hz]
      · simp [ports,hp,hk]
  · simp only [ite_true,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hp:p i with
    | inl b=>simp [ports,hp]
    | inr t=>
      rcases t with ⟨k,s⟩
      by_cases hk:k=j
      · subst k;cases s <;> simp [ports,hp,hz]
      · simp [ports,hp,hk]

theorem residue (p : Fin n→Port 7) (u : Fin 3→Bool) (j : Fin 7) :
    W.residue (ports p (A.codeSeven u)) j=Q.translated (W.residue p) u j := by
  simp only [W.residue,incidence,Q.translated]
  split_ifs <;> simp

theorem code_translation (u z : Fin 3→Bool) :
    (fun j=>A.codeSeven u j ^^ A.codeSeven z j)=A.codeSeven (fun i=>u i ^^ z i) := by
  revert u z
  decide

theorem code_value (p : Fin n→Port 7) (u z : Fin 3→Bool) :
    word (ports p (A.codeSeven u)) (A.codeSeven z)=
      word p (A.codeSeven (fun i=>u i ^^ z i)) := by
  rw [value,code_translation]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceTranslation
end
