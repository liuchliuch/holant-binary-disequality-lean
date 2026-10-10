import Holant.Projective.CyclicDressing.RootMap

/-! Four literal native-X binary attachments and their exact Walsh-coordinate
normalization. These are finite-sum identities on the original physical inputs;
no analytic basis change or scalar division is declared gadget-realizable. -/
noncomputable section
namespace Holant.Projective.CyclicDressing
open CyclicPhasePencil CyclicQuaternary.Physical

/-- Binary port0 is the exposed output; its port1 joins original q port i via X. -/
def physicalDressing {n : ℕ} (q : Signature Scalar n) (C : Fin n → Mat) : Signature Scalar n :=
  Signature.coordinateAction (fun i => Kernel.mul (C i) Signature.disequality) q

/-- Expands every original bit and every attachment's internal bit separately. -/
theorem physicalDressing_finite_sum {n : ℕ} (q : Signature Scalar n) (C : Fin n → Mat)
    (x : Fin n → Bool) : physicalDressing q C x=
      ∑ y : Fin n → Bool, ∑ z : Fin n → Bool,
        (∏ i, C i (x i) (z i)*Signature.disequality (z i) (y i))*q y := by
  unfold physicalDressing Signature.coordinateAction
  simp only [Kernel.mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Fintype.prod_sum,Finset.sum_mul]

theorem local_walsh_attachment (C : Mat) :
    Kernel.mul (Kernel.mul Pinv (Kernel.mul C Signature.disequality)) P=
      Kernel.mul (walshBinary C) ((2 : Scalar) • Z) := by
  funext a b
  cases a <;> cases b <;> simp [walshBinary,Kernel.mul,Kernel.transpose,Pinv,P,Z,diagonal,Signature.disequality] <;> ring

theorem local_phase_attachment (C : Mat) (r κ : Scalar)
    (hC : walshBinary C=κ • Kernel.mul (phase r) Z) :
    Kernel.mul (Kernel.mul Pinv (Kernel.mul C Signature.disequality)) P=(2*κ) • phase r := by
  rw [local_walsh_attachment,hC]
  funext a b
  cases a <;> cases b <;> simp [Kernel.mul,phase,Z,diagonal] <;> ring

/-- Exact finite-sum transport for all port attachments simultaneously. -/
theorem walsh_physicalDressing {n : ℕ} (q : Signature Scalar n) (C : Fin n → Mat) :
    walsh (physicalDressing q C)=Signature.coordinateAction
      (fun i => Kernel.mul (Kernel.mul Pinv (Kernel.mul (C i) Signature.disequality)) P) (walsh q) := by
  have hq : Signature.coordinateAction (fun _ : Fin n => P) (walsh q)=q :=
    Signature.coordinateAction_cancel _ _ (fun _ => P_Pinv) q
  calc
    walsh (physicalDressing q C)=
        Signature.coordinateAction (fun _ => Pinv)
          (Signature.coordinateAction (fun i => Kernel.mul (C i) Signature.disequality)
            (Signature.coordinateAction (fun _ => P) (walsh q))) := by rw [hq]; rfl
    _ = _ := by
      rw [Signature.coordinateAction_comp,Signature.coordinateAction_comp]

/-- Ordered diagonal tensor action keeps the literal coefficient at each word. -/
theorem phase_action {n : ℕ} (q : Signature Scalar n) (r δ : Fin n → Scalar)
    (x : Fin n → Bool) :
    Signature.coordinateAction (fun i => (δ i) • phase (r i)) q x=
      (∏ i, δ i)*(∏ i, (r i)^(if x i then 1 else 0))*q x := by
  unfold Signature.coordinateAction
  rw [Fintype.sum_eq_single x]
  · simp only [Pi.smul_apply,smul_eq_mul,phase,diagonal,ite_true]
    rw [Finset.prod_mul_distrib]
    congr 2
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> simp
  · intro y hy
    have hne : ∃ i, x i≠y i := by
      by_contra h
      push_neg at h
      exact hy (funext (fun i => (h i).symm))
    obtain ⟨i,hi⟩ := hne
    have hz : (∏ j, ((δ j) • phase (r j)) (x j) (y j))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [phase,diagonal,hi]
    rw [hz,zero_mul]

/-- The source scalar is exactly 2^4 times the product of the four recorded
representative scalars, with one factor2 per actual native attachment. -/
theorem walsh_dressing_coeff (q : Signature Scalar 4) (C : Fin 4 → Mat) (r κ : Fin 4 → Scalar)
    (hC : ∀ i, walshBinary (C i)=κ i • Kernel.mul (phase (r i)) Z) (x : Fin 4 → Bool) :
    walsh (physicalDressing q C) x=
      ((2 : Scalar)^4*∏ i,κ i) * (walsh q x*∏ i,(r i)^(if x i then 1 else 0)) := by
  rw [walsh_physicalDressing]
  have hlocal : (fun i => Kernel.mul (Kernel.mul Pinv (Kernel.mul (C i) Signature.disequality)) P)=
      (fun i => (2*κ i) • phase (r i)) := funext (fun i => local_phase_attachment _ _ _ (hC i))
  rw [hlocal,phase_action]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Fintype.card_fin,Finset.card_univ]
  ring

theorem dressing_scalar_ne_zero (κ : Fin 4 → Scalar) (hκ : ∀ i,κ i≠0) :
    (2 : Scalar)^4*(∏ i,κ i)≠0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hκ i))

/-- The displayed normalized h has exactly the source coefficient formula;
normalization is an analytic equality, with its scalar separately retained. -/
theorem normalized_dressing_coeff (q : Signature Scalar 4) (C : Fin 4 → Mat) (r κ : Fin 4 → Scalar)
    (hκ : ∀ i,κ i≠0) (hC : ∀ i, walshBinary (C i)=κ i • Kernel.mul (phase (r i)) Z)
    (x : Fin 4 → Bool) :
    (((2 : Scalar)^4*∏ i,κ i)⁻¹ • walsh (physicalDressing q C)) x=
      walsh q x*∏ i,(r i)^(if x i then 1 else 0) := by
  simp only [Pi.smul_apply,smul_eq_mul,walsh_dressing_coeff q C r κ hC]
  rw [← mul_assoc,inv_mul_cancel₀ (dressing_scalar_ne_zero κ hκ),one_mul]

/-- Physical source hypotheses use the same actual retained-family phase
representatives as7.2; the original q remains distinct from its Walsh table. -/
theorem source_dressing_coeff {m : ℕ} (F : SignatureFamily Scalar) (hF : F.Finite)
    (q : Signature Scalar 4) (hq : Gadget.Realizes F .disequality q)
    (reps : CyclicQuaternary.Physical.Representatives F m) (r : Roots m) (x : Fin 4 → Bool) :
    (((2 : Scalar)^4*∏ i,reps.scalar (r i))⁻¹ •
      walsh (physicalDressing q (fun i => reps.matrix (r i)))) x=
      walsh q x*∏ i,(r i).val^(if x i then 1 else 0) :=
  normalized_dressing_coeff q (fun i => reps.matrix (r i)) (fun i => (r i).val)
    (fun i => reps.scalar (r i)) (fun i => reps.scalar_ne_zero (r i)) (fun i => reps.walsh_form (r i)) x

end Holant.Projective.CyclicDressing
