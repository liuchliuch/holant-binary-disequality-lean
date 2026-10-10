import Holant.Proofs.Closure.ClosureSixPortSupportContradiction

/-! NEW UNVERIFIED Boolean support normalization transport. Only the actual
phase-one card is transported through the port permutation and bit flips.
No transformed signature is asserted retained and no flipped all-phase deck
is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant

def gaugeWord (e : Equiv.Perm (Fin 6)) (flip : Word 6) : Word 6 ≃ Word 6 where
  toFun w i := w (e.symm i) ^^ flip (e.symm i)
  invFun w i := w (e i) ^^ flip i
  left_inv w := by funext i; simp [Bool.xor_assoc]
  right_inv w := by funext i; simp [Bool.xor_assoc]

@[simp] theorem gaugeWord_apply_at (e : Equiv.Perm (Fin 6)) (flip : Word 6) (w : Word 6) (i : Fin 6) :
    gaugeWord e flip w (e i) = (w i ^^ flip i) := by simp [gaugeWord]

theorem xor_interchange (a b c d : Bool) : ((a^^c)^^(b^^d))=((a^^b)^^(c^^d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xorRight_injective (c : Bool) : Function.Injective (fun b : Bool => b^^c) := by
  intro a b h
  cases a <;> cases b <;> cases c <;> simp_all

def pairFlip (order : Equiv.Perm (Fin 6)) (flip : Word 6) : Bool := flip (order 0) ^^ flip (order 1)

theorem gauge_pair_parity (e order : Equiv.Perm (Fin 6)) (flip : Word 6) (w : Word 6) :
    (gaugeWord e flip w ((order.trans e) 0) ^^ gaugeWord e flip w ((order.trans e) 1)) =
      ((w (order 0) ^^ w (order 1)) ^^ pairFlip order flip) := by
  simp only [Equiv.trans_apply,gaugeWord_apply_at,pairFlip]
  exact xor_interchange _ _ _ _

theorem residualSix_gauge (e order : Equiv.Perm (Fin 6)) (flip : Word 6) (w : Word 6) :
    residualSix (order.trans e) (gaugeWord e flip w) =
      fun i => residualSix order w i ^^ flip (order i.succ.succ) := by
  funext i
  simp [residualSix]

/-- The SAME selected physical support, with its literal parity flip tags. -/
theorem selectedWords_image_gauge (S : Finset (Word 6)) (e order : Equiv.Perm (Fin 6))
    (flip : Word 6) (p : Bool) :
    selectedWords (S.image (gaugeWord e flip)) (order.trans e) (p ^^ pairFlip order flip) =
      (selectedWords S order p).image (gaugeWord e flip) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_filter.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hs
    apply Finset.mem_image.mpr
    refine ⟨w,Finset.mem_filter.mpr ⟨hw,?_⟩,rfl⟩
    rw [gauge_pair_parity] at hp
    exact xorRight_injective _ hp
  · intro hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hs,hp⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨w,hs,rfl⟩,?_⟩
    rw [gauge_pair_parity,hp]

/-- One nonzero lift per word survives all literal coordinate flips. -/
theorem selectedWords_gauge_injective (S : Finset (Word 6)) (e order : Equiv.Perm (Fin 6))
    (flip : Word 6) (p : Bool)
    (injective : Set.InjOn (residualSix order) {w | w ∈ selectedWords S order p}) :
    Set.InjOn (residualSix (order.trans e))
      {w | w ∈ selectedWords (S.image (gaugeWord e flip)) (order.trans e) (p ^^ pairFlip order flip)} := by
  intro x hx y hy same
  have hx' : x ∈ (selectedWords S order p).image (gaugeWord e flip) := by
    rw [←selectedWords_image_gauge]; exact hx
  have hy' : y ∈ (selectedWords S order p).image (gaugeWord e flip) := by
    rw [←selectedWords_image_gauge]; exact hy
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx'
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy'
  rw [residualSix_gauge,residualSix_gauge] at same
  have remaining : residualSix order u = residualSix order v := by
    funext i
    exact xorRight_injective _ (congrFun same i)
  exact congrArg (gaugeWord e flip) (injective hu hv remaining)

theorem selectedWords_gauge_card (S : Finset (Word 6)) (e order : Equiv.Perm (Fin 6))
    (flip : Word 6) (p : Bool) :
    (selectedWords (S.image (gaugeWord e flip)) (order.trans e) (p ^^ pairFlip order flip)).card =
      (selectedWords S order p).card := by
  rw [selectedWords_image_gauge]
  exact Finset.card_image_iff.mpr (gaugeWord e flip).injective.injOn

/-- The atlas's six/eight-word card is a card of the ORIGINAL tensor. -/
theorem gauge_normalized_actual_card_support (edge : Fin 6) (a b o : Bool)
    (notMatching : ¬ (edge=0 ∧ a=false ∧ b=true)) (e : Equiv.Perm (Fin 6)) (flip : Word 6)
    (h : Signature ℂ 6)
    (support : ∀ w, h w ≠ 0 ↔ w ∈ (flatSupport edge a b o).image (gaugeWord e flip)) :
    ∃ order : Equiv.Perm (Fin 6), ∃ p : Bool, ∃ T : Finset (Word 4),
      (T.card=6 ∨ T.card=8) ∧ (∀ x, phaseCard h order p 1 x ≠ 0 ↔ x ∈ T) := by
  obtain ⟨order,p,injective,card⟩ := normalized_projection_choice edge a b o notMatching
  let S := (flatSupport edge a b o).image (gaugeWord e flip)
  let newOrder := order.trans e
  let newParity := p ^^ pairFlip order flip
  have newInjective := selectedWords_gauge_injective _ e order flip p injective
  refine ⟨newOrder,newParity,selectedOutputs S newOrder newParity,?_,?_⟩
  · rw [selectedOutputs_card _ _ _ newInjective,selectedWords_gauge_card]
    exact card
  · exact phase_one_support h S support newOrder newParity newInjective

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
