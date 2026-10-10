import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsCaps

/-! Bounded cap-ratio connectivity. If a pair cannot be joined by actual
nonzero antidiagonal transfers, the literal complementary cap sums force all
four port-weight squares equal. The remaining ratios use only cap composition
and reversed binary boundary order, without any spectral assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsConnectivity
open Holant Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace R
export PaperTerminalBridgeEqualProductsCaps (Rel refl symm trans cap_relation)
end R
namespace G
export EightVertexGaugeCaps (loopPorts remainingPorts)
export StableDenseResidualGaugeCore (weighted)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem squares_of_sum_zero {a b : K} (h : a+b=0) : a^2=b^2 := by
  rw [eq_neg_of_add_eq_zero_left h]
  ring

theorem squares_of_unrelated (F : SignatureFamily K) (u : Fin 4→K) (live : ∀i,u i≠0)
    (caps : ∀k : Fin 6,u (G.loopPorts k).1+u (G.loopPorts k).2≠0→
      R.Rel F (u (G.remainingPorts k).1) (u (G.remainingPorts k).2))
    (missing : ¬R.Rel F (u 0) (u 1)) : ∀i,u i^2=u 0^2 := by
  classical
  have h23 : u 2+u 3=0 := by by_contra h;exact missing (caps 5 h)
  by_cases r02 : R.Rel F (u 0) (u 2)
  · have n12 : ¬R.Rel F (u 1) (u 2) := fun h=>missing
      (R.trans F _ _ _ (live 2) r02 (R.symm F _ _ h))
    have h03 : u 0+u 3=0 := by by_contra h;exact n12 (caps 2 h)
    have r13 : R.Rel F (u 1) (u 3) := by
      by_contra h
      have h02 : u 0+u 2=0 := by by_contra bad;exact h (caps 1 bad)
      have twice : (2:K)*u 0=0 := by linear_combination h03+h02-h23
      exact (mul_ne_zero (by norm_num) (live 0)) twice
    have n03 : ¬R.Rel F (u 0) (u 3) := fun h=>missing
      (R.trans F _ _ _ (live 3) h (R.symm F _ _ r13))
    have h12 : u 1+u 2=0 := by by_contra h;exact n03 (caps 3 h)
    have h3 : u 3^2=u 0^2 := (squares_of_sum_zero h03).symm
    have h2 : u 2^2=u 0^2 := (squares_of_sum_zero h23).trans h3
    have h1 : u 1^2=u 0^2 := (squares_of_sum_zero h12).trans h2
    intro i;fin_cases i
    · rfl
    · exact h1
    · exact h2
    · exact h3
  · have h13 : u 1+u 3=0 := by by_contra h;exact r02 (caps 4 h)
    have r03 : R.Rel F (u 0) (u 3) := by
      by_contra h
      have h12 : u 1+u 2=0 := by by_contra bad;exact h (caps 3 bad)
      have twice : (2:K)*u 1=0 := by linear_combination h13+h12-h23
      exact (mul_ne_zero (by norm_num) (live 1)) twice
    have n13 : ¬R.Rel F (u 1) (u 3) := fun h=>missing (R.symm F _ _
      (R.trans F _ _ _ (live 3) h (R.symm F _ _ r03)))
    have h02 : u 0+u 2=0 := by by_contra h;exact n13 (caps 1 h)
    have h2 : u 2^2=u 0^2 := (squares_of_sum_zero h02).symm
    have h3 : u 3^2=u 0^2 := (squares_of_sum_zero h23).symm.trans h2
    have h1 : u 1^2=u 0^2 := (squares_of_sum_zero h13).trans h3
    intro i;fin_cases i
    · rfl
    · exact h1
    · exact h2
    · exact h3

theorem relatives_of_caps (F : SignatureFamily K) (u : Fin 4→K) (live : ∀i,u i≠0)
    (different : ¬∀i,u i^2=u 0^2)
    (caps : ∀e : Equiv.Perm (Fin 4),∀k : Fin 6,
      u (e.symm (G.loopPorts k).1)+u (e.symm (G.loopPorts k).2)≠0→
      R.Rel F (u (e.symm (G.remainingPorts k).1)) (u (e.symm (G.remainingPorts k).2))) :
    ∀i,R.Rel F (u i) (u 0) := by
  classical
  intro i
  by_cases zero : i=0
  · subst i;exact R.refl F _ (live 0)
  let e : Equiv.Perm (Fin 4) := Equiv.swap 1 i
  have e0 : e 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm zero)
  have v0 : u (e.symm 0)=u 0 := by simp only [e,Equiv.symm_swap];rw [e0]
  have v1 : u (e.symm 1)=u i := by simp [e]
  have relation : R.Rel F (u (e.symm 0)) (u (e.symm 1)) := by
    by_contra absent
    have same := squares_of_unrelated F (fun j=>u (e.symm j)) (fun j=>live _) (caps e) absent
    apply different
    intro j
    have h := same (e j)
    simpa only [Equiv.symm_apply_apply,v0] using h
  rw [v0,v1] at relation
  exact R.symm F _ _ relation

theorem weighted_relatives (F : SignatureFamily K) (a : K) (u : Fin 4→K)
    (scale : a≠0) (live : ∀i,u i≠0) (actual : Gadget.Realizes F .disequality (G.weighted a u))
    (different : ¬∀i,u i^2=u 0^2) : ∀i,R.Rel F (u i) (u 0) := by
  apply relatives_of_caps F u live different
  intro e k sum
  have moved := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ actual e.symm
  simp only [Equiv.symm_symm] at moved
  rw [Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePorts.weighted_reindex] at moved
  exact R.cap_relation F a (fun i=>u (e.symm i)) scale moved k sum

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsConnectivity
end
