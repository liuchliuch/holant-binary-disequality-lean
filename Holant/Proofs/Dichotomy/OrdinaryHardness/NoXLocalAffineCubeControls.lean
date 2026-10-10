import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalAffineCubeWitness

/-! The selected pin or signed identification fixes the entire bad cube,
not merely its base point. These are literal coordinate identities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalAffineCubeControls
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.AffinePatching
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {r : ℕ}

theorem corner_outside (z : Word r) (i j k p : Fin r)
    (outside : p∉({i,j,k} : Finset (Fin r))) (v : Fin 8) :
    cubeWords z (basis i) (basis j) (basis k) v p=z p := by
  have pi : p≠i := by simpa using (fun h : p=i=>outside (by simp [h]))
  have pj : p≠j := by intro h;exact outside (by simp [h])
  have pk : p≠k := by intro h;exact outside (by simp [h])
  fin_cases v <;> simp [cubeWords,AffinePhase.xor,basis,pi,pj,pk,Ne.symm pi,Ne.symm pj,Ne.symm pk]

theorem pin_or_signed_pair_corners (higher : 5≤r) (a z : Word r) (i j k : Fin r) :
    (∃p : Fin r,p∉({i,j,k} : Finset (Fin r)) ∧
      ∀v : Fin 8,cubeWords z (basis i) (basis j) (basis k) v p=a p) ∨
    (∃p q : Fin r,p∉({i,j,k} : Finset (Fin r)) ∧ q∉({i,j,k} : Finset (Fin r)) ∧ p≠q ∧
      ∀v : Fin 8,(cubeWords z (basis i) (basis j) (basis k) v p ^^
        cubeWords z (basis i) (basis j) (basis k) v q)=(a p ^^ a q)) := by
  rcases NoXLocalAffineCubeWitness.pin_or_signed_pair higher a z i j k with pin|pair
  · obtain ⟨p,hp,equal⟩ := pin
    exact Or.inl ⟨p,hp,fun v=>(corner_outside z i j k p hp v).trans equal.symm⟩
  · obtain ⟨p,q,hp,hq,different,equal⟩ := pair
    refine Or.inr ⟨p,q,hp,hq,different,?_⟩
    intro v
    rw [corner_outside z i j k p hp v,corner_outside z i j k q hq v]
    exact equal.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalAffineCubeControls
end
