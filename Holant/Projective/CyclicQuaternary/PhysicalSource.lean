import Holant.Projective.CyclicQuaternary.Physical

/-! Physical-source specialization of Lemma 7.2. The original q, finite retained
family, actual binary representatives, native-X convention, inverse Walsh action,
and each recorded nonzero scalar remain explicit. Division is an analytic
normalization of the resulting card, never a realizability operation. -/
noncomputable section
namespace Holant.Projective.CyclicQuaternary.Physical
open CyclicPhasePencil Holant.Tractable

/-- One fixed actual ordered representative for every literal finite-order root. -/
abbrev Root (m : ℕ) := {s : Scalar // s^m=1}

structure Representatives (F : SignatureFamily Scalar) (m : ℕ) where
  matrix : Root m → Mat
  scalar : Root m → Scalar
  scalar_ne_zero : ∀ s, scalar s≠0
  actual : ∀ s, Gadget.Realizes F .disequality (kernelSignature (matrix s))
  walsh_form : ∀ s, walshBinary (matrix s)=scalar s • Kernel.mul (phase s.val) Z

theorem closing_phase (s κ : Scalar) :
    Kernel.mul (Kernel.mul ((2 : Scalar) • Z) (κ • Kernel.mul (phase s) Z)) ((2 : Scalar) • Z)=
      (4*κ) • diagonal 1 (-s) := by
  funext a b
  cases a <;> cases b <;> simp [Kernel.mul,phase,Z,diagonal] <;> ring

theorem walsh_physicalCard_phase (q : Signature Scalar 4) (i : Fin 3) (side : Bool)
    (C : Mat) (s κ : Scalar) (hC : walshBinary C=κ • Kernel.mul (phase s) Z) :
    walshBinary (physicalCard q i side C)=(4*κ) • contraction (walsh q) i side s := by
  rw [walsh_physicalCard,hC,closing_phase]
  funext u v
  simp [contractKernel,contraction,Finset.mul_sum,mul_assoc]
  ring

theorem walshBinary_transpose (C : Mat) : walshBinary (Kernel.transpose C)=Kernel.transpose (walshBinary C) := by
  funext a b
  cases a <;> cases b <;> simp [walshBinary,Kernel.mul,Kernel.transpose,Pinv,P] <;> ring

def orderedPhysicalCard (q : Signature Scalar 4) (i : Fin 3) (side order : Bool) (C : Mat) : Mat :=
  if order then Kernel.transpose (physicalCard q i side C) else physicalCard q i side C

def physicalTransfer (q : Signature Scalar 4) (i : Fin 3) (side order : Bool) (C : Mat) : Mat :=
  Kernel.mul (walshBinary (orderedPhysicalCard q i side order C)) Z

/-- Two native edges produce exactly the recorded factor 4*kappa, at either
ordered residual boundary. The remaining tensor is the previously classified card. -/
theorem physicalTransfer_phase (q : Signature Scalar 4) (i : Fin 3) (side order : Bool)
    (C : Mat) (s κ : Scalar) (hC : walshBinary C=κ • Kernel.mul (phase s) Z) :
    physicalTransfer q i side order C=(4*κ) • transferCard (walsh q) i side order s := by
  unfold physicalTransfer orderedPhysicalCard transferCard orderedContraction
  cases order
  · simp only [Bool.false_eq_true,ite_false,walsh_physicalCard_phase q i side C s κ hC]
    funext a b
    simp [Kernel.mul,Finset.mul_sum,mul_assoc]
    ring
  · simp only [ite_true,walshBinary_transpose,walsh_physicalCard_phase q i side C s κ hC]
    funext a b
    simp [Kernel.mul,Kernel.transpose,Finset.mul_sum,mul_assoc]
    ring

/-- Explicit analytic division by the actual nonzero recorded scalar. -/
theorem normalized_physicalTransfer (q : Signature Scalar 4) (i : Fin 3) (side order : Bool)
    (C : Mat) (s κ : Scalar) (hκ : κ≠0) (hC : walshBinary C=κ • Kernel.mul (phase s) Z) :
    (4*κ)⁻¹ • physicalTransfer q i side order C=transferCard (walsh q) i side order s := by
  rw [physicalTransfer_phase q i side order C s κ hC,smul_smul]
  have hn : (4 : Scalar)*κ≠0 := mul_ne_zero (by norm_num) hκ
  rw [inv_mul_cancel₀ hn,one_smul]

theorem isPhase_smul_iff (m : ℕ) (lam : Scalar) (hlam : lam≠0) (T : Mat) :
    IsPhase m (lam • T) ↔ IsPhase m T := by
  constructor
  · rintro ⟨η,δ,hη,hδ,h⟩
    refine ⟨η,lam⁻¹*δ,hη,mul_ne_zero (inv_ne_zero hlam) hδ,?_⟩
    have hh := congrArg (fun M : Mat => lam⁻¹ • M) h
    simpa only [smul_smul,inv_mul_cancel₀ hlam,one_smul] using hh
  · rintro ⟨η,δ,hη,hδ,h⟩
    exact ⟨η,lam*δ,hη,mul_ne_zero hlam hδ,by rw [h,smul_smul]⟩

theorem zero_or_phase_smul_iff (m : ℕ) (lam : Scalar) (hlam : lam≠0) (T : Mat) :
    (lam • T=0 ∨ IsPhase m (lam • T)) ↔ (T=0 ∨ IsPhase m T) := by
  rw [isPhase_smul_iff m lam hlam]
  simp [smul_eq_zero,hlam]

def PhysicalCards {F : SignatureFamily Scalar} {m : ℕ} (reps : Representatives F m)
    (q : Signature Scalar 4) : Prop :=
  ∀ (i : Fin 3) (side order : Bool) (s : Root m),
    physicalTransfer q i side order (reps.matrix s)=0 ∨
      IsPhase m (physicalTransfer q i side order (reps.matrix s))

/-- Source card membership is invariant under the explicitly recorded nonzero
normalization; the original q is transformed, never silently identified with it. -/
theorem physicalCards_iff {F : SignatureFamily Scalar} {m : ℕ}
    (reps : Representatives F m) (q : Signature Scalar 4) :
    PhysicalCards reps q ↔ AllPhaseCards m (walsh q) := by
  constructor
  · intro h i side order s hs
    have hh := h i side order ⟨s,hs⟩
    rw [physicalTransfer_phase q i side order _ s _ (reps.walsh_form ⟨s,hs⟩)] at hh
    exact (zero_or_phase_smul_iff m _ (mul_ne_zero (by norm_num) (reps.scalar_ne_zero ⟨s,hs⟩)) _).mp hh
  · intro h i side order s
    rw [physicalTransfer_phase q i side order _ s.val _ (reps.walsh_form s)]
    exact (zero_or_phase_smul_iff m _ (mul_ne_zero (by norm_num) (reps.scalar_ne_zero s)) _).mpr
      (h i side order s.val s.property)

/-- Lemma 7.2 with the physical source assumptions retained literally. q is an
actual gadget over the same finite algebraic family as all phase representatives;
its Walsh table is defined by the explicit inverse action. The conclusion and
converse concern its original eight Walsh coefficients and normalized actual cards. -/
theorem source_cyclic_quaternary_phase_family {m : ℕ} (hm : 3≤m)
    (F : SignatureFamily Scalar) (hF : F.Finite) (q : Signature Scalar 4)
    (hq : Gadget.Realizes F .disequality q) (reps : Representatives F m)
    (heven : EvenSupported (walsh q)) :
    PhysicalCards reps q ↔
      NonzeroFamily m (endpoint0 (walsh q)) (endpoint1 (walsh q)) (coordinates (walsh q)) ∨
      ZeroFamily m (endpoint0 (walsh q)) (endpoint1 (walsh q)) (coordinates (walsh q)) := by
  rw [physicalCards_iff]
  exact cyclic_quaternary_phase_family hm (walsh q) heven

end Holant.Projective.CyclicQuaternary.Physical
