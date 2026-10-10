import Holant.ReedMuller.WeightTwoIntegration.Perfection

/-! The derived original weight-two matching is enumerated by its actual
ordered endpoint pairs. Logical coordinates retain the original port map. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
variable {ι : Type*}

 def graphPairing (W : SimpleGraph ι)
    (hmatch : ∀u v w,W.Adj u v → W.Adj u w → v=w)
    (hperfect : ∀x,∃y,W.Adj x y) : Pairing ι where
  mate x := Classical.choose (hperfect x)
  involutive x := (hmatch _ x _ (Classical.choose_spec (hperfect x)).symm
    (Classical.choose_spec (hperfect (Classical.choose (hperfect x))))).symm
  ne_self x := (Classical.choose_spec (hperfect x)).ne.symm

 theorem graphPairing_mate (W : SimpleGraph ι)
    (hmatch : ∀u v w,W.Adj u v → W.Adj u w → v=w)
    (hperfect : ∀x,∃y,W.Adj x y) (u v : ι) :
    (graphPairing W hmatch hperfect).mate u=v ↔ W.Adj u v := by
  constructor
  · intro h
    exact h ▸ Classical.choose_spec (hperfect u)
  · intro h
    exact hmatch u _ v (Classical.choose_spec (hperfect u)) h

 variable {n : ℕ}
 abbrev EdgeHeads (M : Pairing (Fin n)) := {i : Fin n // i<M.mate i}

 def headPorts (M : Pairing (Fin n)) : (EdgeHeads M × Bool) ≃ Fin n where
  toFun e := if e.2 then M.mate e.1.val else e.1.val
  invFun i := if h : i<M.mate i then (⟨i,h⟩,false) else
    (⟨M.mate i,by rw [M.involutive]; exact lt_of_le_of_ne (le_of_not_gt h) (M.ne_self i)⟩,true)
  left_inv e := by
    obtain ⟨⟨i,hi⟩,b⟩ := e
    cases b
    · simp [hi]
    · have hn : ¬M.mate i<M.mate (M.mate i) := by rw [M.involutive]; exact not_lt_of_ge (le_of_lt hi)
      simp [hn]
      exact M.involutive i
  right_inv i := by
    by_cases h : i<M.mate i
    · simp [h]
    · simp [h]
      exact M.involutive i

 theorem headPorts_mate (M : Pairing (Fin n)) (e : EdgeHeads M) (b : Bool) :
    M.mate (headPorts M (e,b))=headPorts M (e,!b) := by
  cases b
  · rfl
  · exact M.involutive e.val

 def edgeCount (M : Pairing (Fin n)) : ℕ := Fintype.card (EdgeHeads M)

 def originalPorts (M : Pairing (Fin n)) : (Fin (edgeCount M) × Bool) ≃ Fin n :=
  (Equiv.prodCongr (Fintype.equivFin (EdgeHeads M)).symm (Equiv.refl Bool)).trans (headPorts M)

 theorem originalPorts_mate (M : Pairing (Fin n)) (e : Fin (edgeCount M)) (b : Bool) :
    M.mate (originalPorts M (e,b))=originalPorts M (e,!b) :=
  headPorts_mate M _ b

 theorem twice_edgeCount (M : Pairing (Fin n)) : 2*edgeCount M=n := by
  have hh := Fintype.card_congr (originalPorts M)
  simpa [Fintype.card_prod,Nat.mul_comm] using hh

 def pairedWord {r : ℕ} (p : (Fin r × Bool) ≃ Fin n) (t : Fin r → Bool) : Fin n → Bool :=
  fun i => t (p.symm i).1

 @[simp] theorem pairedWord_port {r : ℕ} (p : (Fin r × Bool) ≃ Fin n) (t : Fin r → Bool)
    (e : Fin r) (b : Bool) : pairedWord p t (p (e,b))=t e := by simp [pairedWord]

 theorem pairing_support_pairedWord (M : Pairing (Fin n)) (t : Fin (edgeCount M) → Bool) :
    M.Support (pairedWord (originalPorts M) t) := by
  intro i
  obtain ⟨⟨e,b⟩,rfl⟩ := (originalPorts M).surjective i
  rw [originalPorts_mate,pairedWord_port,pairedWord_port]

 theorem pairedWord_reconstruct (M : Pairing (Fin n)) (x : Fin n → Bool) (hx : M.Support x) :
    pairedWord (originalPorts M) (fun e => x (originalPorts M (e,false)))=x := by
  funext i
  obtain ⟨⟨e,b⟩,rfl⟩ := (originalPorts M).surjective i
  rw [pairedWord_port]
  cases b
  · rfl
  · have hh := hx (originalPorts M (e,true))
    rwa [originalPorts_mate] at hh

end Holant.ReedMuller.WeightTwoIntegration
