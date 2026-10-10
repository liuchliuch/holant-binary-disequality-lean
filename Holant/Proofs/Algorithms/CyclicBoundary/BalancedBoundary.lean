import Holant.Proofs.Algorithms.CyclicBoundary.CoordinateFactors


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.BalancedBoundary
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing PhysicalAttachments CoordinateFactors
noncomputable section
set_option backward.isDefEq.respectTransparency false

def balanced (p : ℂ) (b : Fin 3 → ℂ) : Signature ℂ 4 :=
  ofCoordinates p p (fun i => (b i,b i))

theorem physical_balanced (p : ℂ) (b : Fin 3 → ℂ) :
    physical (balanced p b) =
      balanced (2*(p+b 0+b 1+b 2))
        ![2*(p+b 0-b 1-b 2),2*(p-b 0+b 1-b 2),2*(p-b 0-b 1+b 2)] := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [physical,Signature.coordinateAction,sum_words,balanced,ofCoordinates,
      hadamard,Fin.prod_univ_succ,h0,h1,h2,h3] <;> ring

theorem balanced_even (p : ℂ) (b : Fin 3 → ℂ) : EvenSupported (balanced p b) :=
  ofCoordinates_even _ _ _

theorem balanced_complement (p : ℂ) (b : Fin 3 → ℂ) (x : Fin 4 → Bool) :
    balanced p b (fun i => !(x i)) = balanced p b x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [balanced,ofCoordinates,h0,h1,h2,h3]

def flip (x y : Fin 4 → Bool) : Fin 4 → Bool := fun i => Bool.xor (x i) (y i)
def translate (q : Signature ℂ 4) (x : Fin 4 → Bool) : Signature ℂ 4 := fun y => q (flip x y)
def signs (x : Fin 4 → Bool) : Fin 4 → ℂ := fun i => if x i then -1 else 1
def toggle (b : Bool) : Kernel ℂ := if b then Signature.disequality else Signature.equality

theorem toggle_entry (b u v : Bool) : toggle b u v = Signature.equality (Bool.xor b u) v := by
  cases b <;> cases u <;> cases v <;> rfl

theorem toggle_action (q : Signature ℂ 4) (x : Fin 4 → Bool) :
    Signature.coordinateAction (fun i => toggle (x i)) q = translate q x := by
  funext y
  simp only [Signature.coordinateAction,toggle_entry]
  change (∑ z, (∏ i, Signature.equality (flip x y i) (z i))*q z) = _
  simp [Signature.prod_equality,translate]

theorem dress_eq_action (q : Signature ℂ 4) (s : Fin 4 → ℂ) :
    dress q s = Signature.coordinateAction (fun i => phase (s i)) q := by
  simpa using (scaled_phase_action q s (fun _ => 1)).symm

theorem phase_inverse (s : ℂ) (hs : s ≠ 0) :
    Kernel.mul (phase (s⁻¹)) (phase s) = Signature.equality ∧
      Kernel.mul (phase s) (phase (s⁻¹)) = Signature.equality := by
  constructor <;> funext u v <;> cases u <;> cases v <;>
    simp [Kernel.mul,PhysicalAttachments.phase,TwoCopyKernels.diagonal,
      Signature.equality,hs]

theorem dress_factor_iff (q : Signature ℂ 4) (s : Fin 4 → ℂ)
    (hs : ∀ i, s i ≠ 0) : HasProperTensorFactor (dress q s) ↔ HasProperTensorFactor q := by
  rw [dress_eq_action]
  exact factor_action_iff q (fun i => phase (s i)) (fun i => phase ((s i)⁻¹))
    (fun i => (phase_inverse _ (hs i)).1) (fun i => (phase_inverse _ (hs i)).2)

theorem sign_intertwining (b : Bool) :
    Kernel.mul hadamard (phase (if b then -1 else 1)) = Kernel.mul (toggle b) hadamard := by
  funext u v
  cases b <;> cases u <;> cases v <;>
    simp [Kernel.mul,hadamard,PhysicalAttachments.phase,TwoCopyKernels.diagonal,
      toggle,Signature.disequality,Signature.equality]

/-- The analytic sign is implemented by an actual retained -1 phase binary;
the equation identifies its physical action with the explicit bit translation. -/
theorem physical_sign_dressing (q : Signature ℂ 4) (x : Fin 4 → Bool) :
    physical (dress q (signs x)) = translate (physical q) x := by
  rw [dress_eq_action]
  unfold physical
  rw [Signature.coordinateAction_comp]
  have he : (fun i => Kernel.mul hadamard (phase (signs x i))) =
      (fun i => Kernel.mul (toggle (x i)) hadamard) := funext (fun i => sign_intertwining (x i))
  rw [he,←Signature.coordinateAction_comp,toggle_action]

theorem toggle_inverse (b : Bool) : Kernel.mul (toggle b) (toggle b) = Signature.equality := by
  cases b <;> simp [toggle,Kernel.disequality_mul_disequality]

theorem translate_factor_iff (q : Signature ℂ 4) (x : Fin 4 → Bool) :
    HasProperTensorFactor (translate q x) ↔ HasProperTensorFactor q := by
  rw [←toggle_action]
  exact factor_action_iff q (fun i => toggle (x i)) (fun i => toggle (x i))
    (fun i => toggle_inverse (x i)) (fun i => toggle_inverse (x i))

theorem odd_flip : ∀ x y : Fin 4 → Bool, odd (flip x y) = Bool.xor (odd x) (odd y) := by
  decide

theorem translate_even {q : Signature ℂ 4} (hq : EvenSupported q)
    (x : Fin 4 → Bool) (hx : odd x=false) : EvenSupported (translate q x) := by
  intro y hy
  apply hq
  rw [odd_flip,hx,hy]
  rfl

/-- The actual retained root family supplies all translation gadgets. The
input is a concrete balanced Walsh table, not a hypothesized terminal. -/
theorem balanced_to_endpoint {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (hN : Even N) (p : ℂ) (b : Fin 3 → ℂ)
    (hq : Gadget.RealizesUpTo F .disequality (physical (balanced p b)))
    (hn : physical (balanced p b) ≠ 0)
    (hp : ¬HasProperTensorFactor (physical (balanced p b))) :
    ∃ x : Fin 4 → Bool,
      Gadget.RealizesUpTo F .disequality (translate (physical (balanced p b)) x) ∧
      EvenSupported (translate (physical (balanced p b)) x) ∧
      translate (physical (balanced p b)) x (fun _ => false) ≠ 0 ∧
      translate (physical (balanced p b)) x (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor (translate (physical (balanced p b)) x) := by
  classical
  have hex : ∃ x, physical (balanced p b) x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨x,hx⟩ := hex
  have he : EvenSupported (physical (balanced p b)) := by
    rw [physical_balanced]
    exact balanced_even _ _
  have hodd : odd x=false := by
    cases ho : odd x
    · rfl
    · exact (hx (he x ho)).elim
  have hroot : ∀ i, (signs x i)^N=1 := by
    intro i
    cases x i <;> simp [signs,hN.neg_pow]
  have hreal := phase_dressing_upTo R (balanced p b) hq (signs x) hroot
  rw [physical_sign_dressing] at hreal
  refine ⟨x,hreal,translate_even he x hodd,?_,?_,
    fun h => hp ((translate_factor_iff _ x).mp h)⟩
  · have hf : BalancedBoundary.flip x (fun _ => false) = x := by
      funext i
      change Bool.xor (x i) false = x i
      cases x i <;> rfl
    change physical (balanced p b) (BalancedBoundary.flip x (fun _ => false)) ≠ 0
    rwa [hf]
  · have hc : physical (balanced p b) (fun i => !(x i)) = physical (balanced p b) x := by
      rw [physical_balanced]
      exact balanced_complement _ _ x
    have hf : BalancedBoundary.flip x (fun _ => true) = (fun i => !(x i)) := by
      funext i
      change Bool.xor (x i) true = !(x i)
      cases x i <;> rfl
    change physical (balanced p b) (BalancedBoundary.flip x (fun _ => true)) ≠ 0
    rwa [hf, hc]

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.BalancedBoundary
