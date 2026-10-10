import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointDressing
import Holant.OpenNetworkComposition.Closure


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.PhysicalAttachments
open ZeroEndpointDressing TwoCopyKernels Holant.OpenNetworkComposition
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binary (C : Kernel ℂ) : Signature ℂ 2 := fun x => C (x 0) (x 1)
def phase (s : ℂ) : Kernel ℂ := diagonal 1 s

def attach (q : Signature ℂ 4) (i : Fin 4) (C : Kernel ℂ) : Signature ℂ 4 :=
  Signature.coordinateAction
    (fun j => if j=i then Kernel.mul C Signature.disequality else Signature.equality) q

def attachAll (q : Signature ℂ 4) (C : Fin 4 → Kernel ℂ) : Signature ℂ 4 :=
  Signature.coordinateAction (fun i => Kernel.mul (C i) Signature.disequality) q

theorem update_word (x : Fin 4 → Bool) (i : Fin 4) (b : Bool) :
    Function.update x i b = ![if 0=i then b else x 0,if 1=i then b else x 1,
      if 2=i then b else x 2,if 3=i then b else x 3] := by
  funext j
  fin_cases j <;> simp [Function.update_apply]

theorem attach_eq_splice (q : Signature ℂ 4) (i : Fin 4) (C : Kernel ℂ) :
    attach q i C = spliceTensor q (binary C) i := by
  funext x
  have hx : x = ![x 0,x 1,x 2,x 3] := by funext j; fin_cases j <;> rfl
  rw [hx]
  fin_cases i <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [attach,spliceTensor,binary,Signature.coordinateAction,sum_words,
      Kernel.mul,Signature.equality,Signature.disequality,Fin.prod_univ_succ,
      update_word,h0,h1,h2,h3] <;> ring

theorem realizes_attach (F : SignatureFamily ℂ) (q : Signature ℂ 4)
    (i : Fin 4) (C : Kernel ℂ) (hq : Gadget.Realizes F .disequality q)
    (hC : Gadget.Realizes F .disequality (binary C)) :
    Gadget.Realizes F .disequality (attach q i C) := by
  rw [attach_eq_splice]
  exact realizes_splice F q (binary C) hq hC i

theorem four_attachments (q : Signature ℂ 4) (C : Fin 4 → Kernel ℂ) :
    attach (attach (attach (attach q 0 (C 0)) 1 (C 1)) 2 (C 2)) 3 (C 3) =
      attachAll q C := by
  simp only [attach,Signature.coordinateAction_comp,attachAll]
  congr 1
  funext i
  fin_cases i <;> simp [Kernel.equality_mul,Kernel.mul_equality]

theorem realizes_attachAll (F : SignatureFamily ℂ) (q : Signature ℂ 4)
    (C : Fin 4 → Kernel ℂ) (hq : Gadget.Realizes F .disequality q)
    (hC : ∀ i, Gadget.Realizes F .disequality (binary (C i))) :
    Gadget.Realizes F .disequality (attachAll q C) := by
  rw [←four_attachments]
  exact realizes_attach F _ 3 _
    (realizes_attach F _ 2 _ (realizes_attach F _ 1 _
      (realizes_attach F q 0 _ hq (hC 0)) (hC 1)) (hC 2)) (hC 3)

theorem action_scale (A : Fin 4 → Kernel ℂ) (q : Signature ℂ 4) (c : ℂ) :
    Signature.coordinateAction A (c • q) = c • Signature.coordinateAction A q := by
  funext x
  simp [Signature.coordinateAction,Finset.mul_sum,mul_left_comm,mul_assoc]

theorem scaled_phase_action (q : Signature ℂ 4) (s d : Fin 4 → ℂ) :
    Signature.coordinateAction (fun i => d i • phase (s i)) q =
      (∏ i, d i) • dress q s := by
  funext x
  unfold Signature.coordinateAction
  rw [Fintype.sum_eq_single x]
  · simp only [Pi.smul_apply,smul_eq_mul,phase,diagonal,ite_true]
    rw [Finset.prod_mul_distrib]
    have h : (∏ i, if x i then s i else 1) = ∏ i, (s i)^(if x i then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      cases x i <;> simp
    rw [h]
    simp [dress,mul_comm,mul_left_comm,mul_assoc]
  · intro y hy
    have hn : ∃ i, x i ≠ y i := by
      by_contra h
      push_neg at h
      exact hy (funext (fun i => (h i).symm))
    obtain ⟨i,hi⟩ := hn
    have hz : (∏ j, (d j • phase (s j)) (x j) (y j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [phase,diagonal,hi]
    rw [hz,zero_mul]

/-- Exact matrix data of retained finite-root representatives. This is not a
classification or closure outcome: it gives the actual binary network and
the direct C X P = 2 κ P diag(1,s) calculation in fixed physical coordinates. -/
structure Representatives (F : SignatureFamily ℂ) (N : ℕ) where
  matrix : {s : ℂ // s^N=1} → Kernel ℂ
  scalar : {s : ℂ // s^N=1} → ℂ
  scalar_ne_zero : ∀ s, scalar s ≠ 0
  actual : ∀ s, Gadget.Realizes F .disequality (binary (matrix s))
  action : ∀ s,
    Kernel.mul (Kernel.mul (matrix s) Signature.disequality) hadamard =
      Kernel.mul hadamard ((2*scalar s) • phase s.val)

theorem physical_attachment_formula (q : Signature ℂ 4) (C : Fin 4 → Kernel ℂ)
    (s k : Fin 4 → ℂ)
    (hC : ∀ i, Kernel.mul (Kernel.mul (C i) Signature.disequality) hadamard =
      Kernel.mul hadamard ((2*k i) • phase (s i))) :
    attachAll (physical q) C = ((2:ℂ)^4 * ∏ i, k i) • physical (dress q s) := by
  unfold attachAll physical
  rw [Signature.coordinateAction_comp]
  have he := funext hC
  rw [he,←Signature.coordinateAction_comp,scaled_phase_action,action_scale]
  congr 1
  rw [Finset.prod_mul_distrib]
  simp

/-- Existence of the physical construction is exact; only the resulting
tensor identity, not any supplied resource, contains the recorded scale. -/
theorem actual_phase_dressing {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (q : Signature ℂ 4)
    (hq : Gadget.Realizes F .disequality (physical q))
    (s : Fin 4 → ℂ) (hs : ∀ i, (s i)^N=1) :
    ∃ c : ℂ, c ≠ 0 ∧ Gadget.Realizes F .disequality (c • physical (dress q s)) := by
  let t : Fin 4 → {s : ℂ // s^N=1} := fun i => ⟨s i,hs i⟩
  refine ⟨2^4 * ∏ i, R.scalar (t i),
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => R.scalar_ne_zero (t i))),?_⟩
  rw [←physical_attachment_formula q (fun i => R.matrix (t i)) s
    (fun i => R.scalar (t i)) (fun i => R.action (t i))]
  exact realizes_attachAll F _ _ hq (fun i => R.actual (t i))

theorem dress_scale (q : Signature ℂ 4) (s : Fin 4 → ℂ) (c : ℂ) :
    dress (c • q) s = c • dress q s := by
  funext x
  simp [dress,mul_assoc]

theorem upTo_of_scale {F : SignatureFamily ℂ} (q : Signature ℂ 4)
    (c : ℂ) (hc : c ≠ 0)
    (h : Gadget.RealizesUpTo F .disequality (c • q)) :
    Gadget.RealizesUpTo F .disequality q := by
  obtain ⟨d,hd,h⟩ := h
  refine ⟨d*c,mul_ne_zero hd hc,?_⟩
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using h

theorem phase_dressing_upTo {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo F .disequality (physical q))
    (s : Fin 4 → ℂ) (hs : ∀ i, (s i)^N=1) :
    Gadget.RealizesUpTo F .disequality (physical (dress q s)) := by
  obtain ⟨c,hc,hq⟩ := hq
  have hactual : Gadget.Realizes F .disequality (physical (c • q)) := by
    rw [physical,action_scale]
    exact hq
  obtain ⟨d,hd,h⟩ := actual_phase_dressing R (c • q) hactual s hs
  rw [dress_scale,physical,action_scale,smul_smul] at h
  exact ⟨d*c,mul_ne_zero hd hc,h⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.PhysicalAttachments
