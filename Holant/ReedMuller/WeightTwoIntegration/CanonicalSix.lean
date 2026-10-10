import Holant.ReedMuller.WeightTwoIntegration.Factorization
import Holant.ReedMuller.WeightTwoIntegration.ThreeSquares
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalTopology

/-! The derived three-edge matching is transported to the literal six original
ports used by the exceptional network, with explicit reindex provenance. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.MatchingConsistency Holant.ReedMuller.CoefficientAtlas
set_option backward.isDefEq.respectTransparency false
namespace OriginalPairing
variable {f : Signature ℂ 6}

 def canonicalOrder (C : OriginalPairing f) (hc : C.count=3) : Equiv.Perm (Fin 6) :=
  (ExceptionalTopology.canonicalPorts.symm.trans
    (Equiv.prodCongr (finCongr hc).symm (Equiv.refl Bool))).trans C.ports

 theorem canonicalOrder_port (C : OriginalPairing f) (hc : C.count=3) (e : Fin 3) (b : Bool) :
    C.canonicalOrder hc (ExceptionalTopology.canonicalPorts (e,b))=
      C.ports (Fin.cast hc.symm e,b) := by simp [canonicalOrder]

 theorem canonicalOrder_inverse_port (C : OriginalPairing f) (hc : C.count=3)
    (e : Fin C.count) (b : Bool) :
    (C.canonicalOrder hc).symm (C.ports (e,b))=ExceptionalTopology.canonicalPorts (Fin.cast hc e,b) := by
  apply (C.canonicalOrder hc).injective
  rw [Equiv.apply_symm_apply,C.canonicalOrder_port]
  simp

 private theorem canonical_support (x : Fin 6 → Bool) :
    (∀e : Fin 3,x (ExceptionalTopology.canonicalPorts (e,false))=
      x (ExceptionalTopology.canonicalPorts (e,true))) ↔ x 0=x 1 ∧ x 2=x 3 ∧ x 4=x 5 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := ExceptionalTopology.canonicalPorts_values
  constructor
  · intro h
    exact ⟨by simpa only [h0,h1] using h 0,by simpa only [h2,h3] using h 1,
      by simpa only [h4,h5] using h 2⟩
  · rintro ⟨h01,h23,h45⟩ e
    fin_cases e
    · change x (ExceptionalTopology.canonicalPorts (0,false))=x (ExceptionalTopology.canonicalPorts (0,true))
      rw [h0,h1]; exact h01
    · change x (ExceptionalTopology.canonicalPorts (1,false))=x (ExceptionalTopology.canonicalPorts (1,true))
      rw [h2,h3]; exact h23
    · change x (ExceptionalTopology.canonicalPorts (2,false))=x (ExceptionalTopology.canonicalPorts (2,true))
      rw [h4,h5]; exact h45

 theorem canonical_support_iff (C : OriginalPairing f) (hc : C.count=3) (x : Fin 6 → Bool) :
    C.matching.Support (fun i=>x ((C.canonicalOrder hc).symm i)) ↔ x 0=x 1 ∧ x 2=x 3 ∧ x 4=x 5 := by
  rw [C.support_ports,←canonical_support]
  simp only [C.canonicalOrder_inverse_port]
  constructor
  · intro h e
    simpa using h (Fin.cast hc.symm e)
  · intro h e
    exact h (Fin.cast hc e)

 theorem canonical_logical_word (C : OriginalPairing f) (hc : C.count=3) (x : Fin 6 → Bool) :
    (fun e=>x ((C.canonicalOrder hc).symm (C.ports (e,false))))=
      fun e=>![x 0,x 2,x 4] (Fin.cast hc e) := by
  funext e
  rw [C.canonicalOrder_inverse_port]
  have hh (j : Fin 3) : x (ExceptionalTopology.canonicalPorts (j,false))=![x 0,x 2,x 4] j := by
    obtain ⟨h0,_,h2,_,h4,_⟩ := ExceptionalTopology.canonicalPorts_values
    fin_cases j
    · change x (ExceptionalTopology.canonicalPorts (0,false))=x 0
      rw [h0]
    · change x (ExceptionalTopology.canonicalPorts (1,false))=x 2
      rw [h2]
    · change x (ExceptionalTopology.canonicalPorts (2,false))=x 4
      rw [h4]
  exact hh _

 theorem canonical_analytic (C : OriginalPairing f) (hc : C.count=3) (H : Consistent f)
    (rho : Fin 3 → ℂ) (kap : ℂ)
    (he : ∀a b c,C.threeLogical hc ![a,b,c]=C.logical (fun _=>false)*exceptionalH rho kap a b c) :
    Tensor.reindex (C.canonicalOrder hc).symm f=
      fun x=>C.logical (fun _=>false)*ExceptionalTopology.paired (exceptionalH rho kap) x := by
  funext x
  rw [Tensor.reindex,C.tensor_exact H _,C.canonical_support_iff]
  rw [C.canonical_logical_word]
  have hh := he (x 0) (x 2) (x 4)
  change C.logical (fun e=>![x 0,x 2,x 4] (Fin.cast hc e))=_ at hh
  rw [hh]
  simp only [ExceptionalTopology.paired,mul_ite,mul_zero]
  split_ifs <;> rfl

 theorem canonical_physical (q : Signature ℂ 6) (C : OriginalPairing (walsh q))
    (hc : C.count=3) (H : Consistent (walsh q)) (rho : Fin 3 → ℂ) (kap : ℂ)
    (he : ∀a b c,C.threeLogical hc ![a,b,c]=C.logical (fun _=>false)*exceptionalH rho kap a b c) :
    Tensor.reindex (C.canonicalOrder hc).symm q=
      fun x=>C.logical (fun _=>false)*Signature.coordinateAction (fun _=>walshKernel)
        (ExceptionalTopology.paired (exceptionalH rho kap)) x := by
  have hphys := congrArg (Tensor.reindex (C.canonicalOrder hc).symm) (physical_of_walsh q)
  calc
    _=Tensor.reindex (C.canonicalOrder hc).symm
        (Signature.coordinateAction (fun _=>walshKernel) (walsh q)) := hphys.symm
    _=Signature.coordinateAction (fun _=>walshKernel)
        (Tensor.reindex (C.canonicalOrder hc).symm (walsh q)) :=
      (CoefficientAtlas.coordinateAction_reindex _ _ _).symm
    _=_ := by
      rw [C.canonical_analytic hc H rho kap he]
      funext x
      simp only [Signature.coordinateAction,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

end OriginalPairing
end Holant.ReedMuller.WeightTwoIntegration
