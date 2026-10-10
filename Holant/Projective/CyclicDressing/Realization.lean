import Holant.OpenNetworkComposition.Closure
import Holant.Projective.CyclicDressing.AttachmentComposition

/-! Actual gadget closure needed by Lemma7.3. Four disjoint one-port joins are
performed by the proved full OpenNetwork construction, preserving native-X
edges, all original resource labels, scalar components, and boundary order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Projective.CyclicDressing
open CyclicQuaternary.Physical Holant.Tractable OpenNetworkComposition

theorem update_word4 (w : Fin 4 → Bool) (i : Fin 4) (a : Bool) :
    Function.update w i a=![if 0=i then a else w 0,if 1=i then a else w 1,
      if 2=i then a else w 2,if 3=i then a else w 3] := by
  funext j
  fin_cases j <;> simp [Function.update_apply]

/-- The one-port action is the exact disjoint boundary sum, with binary port0
exposed and port1 connected to q's original selected port. -/
theorem onePort_eq_splice (q : Signature Scalar 4) (C : Mat) (i : Fin 4) :
    onePort q i C=spliceTensor q (kernelSignature C) i := by
  funext x
  have hx : x=![x 0,x 1,x 2,x 3] := by funext j; fin_cases j <;> rfl
  rw [hx]
  fin_cases i <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [onePort,spliceTensor,Signature.coordinateAction,sum_words4,Fin.prod_univ_succ,
      Kernel.mul,Signature.equality,Signature.disequality,kernelSignature,update_word4,h0,h1,h2,h3] <;> ring

/-- No analytically transformed or rescaled signature is used as a resource. -/
theorem realizes_onePort (family : SignatureFamily Scalar) (q : Signature Scalar 4) (C : Mat)
    (hq : Gadget.Realizes family .disequality q)
    (hC : Gadget.Realizes family .disequality (kernelSignature C)) (i : Fin 4) :
    Gadget.Realizes family .disequality (onePort q i C) := by
  rw [onePort_eq_splice]
  exact OpenNetworkComposition.realizes_splice family q (kernelSignature C) hq hC i

/-- Four independent binary gadget copies are attached to the four original
ports. The resulting unnormalized finite sum is an actual gadget over the same
family, even when a supplied realization has free stubs or scalar components. -/
theorem realizes_physicalDressing (family : SignatureFamily Scalar) (q : Signature Scalar 4)
    (C : Fin 4 → Mat) (hq : Gadget.Realizes family .disequality q)
    (hC : ∀i,Gadget.Realizes family .disequality (kernelSignature (C i))) :
    Gadget.Realizes family .disequality (physicalDressing q C) := by
  rw [← four_attachments]
  exact realizes_onePort family _ _
    (realizes_onePort family _ _
      (realizes_onePort family _ _
        (realizes_onePort family q (C 0) hq (hC 0) 0) (hC 1) 1) (hC 2) 2) (hC 3) 3

/-- The actual construction and the exact scalar-normalized Walsh formula from
Lemma7.3 hold together, retaining every recorded phase representative scalar. -/
theorem source_actual_dressing {m : ℕ} (family : SignatureFamily Scalar) (hfamily : family.Finite)
    (q : Signature Scalar 4) (hq : Gadget.Realizes family .disequality q)
    (reps : CyclicQuaternary.Physical.Representatives family m) (r : Roots m) :
    Gadget.Realizes family .disequality (physicalDressing q (fun i => reps.matrix (r i))) ∧
    ((2 : Scalar)^4*∏i,reps.scalar (r i))≠0 ∧
    ∀x : Fin 4 → Bool,
      (((2 : Scalar)^4*∏i,reps.scalar (r i))⁻¹ • walsh (physicalDressing q (fun i => reps.matrix (r i)))) x=
        walsh q x*∏i,(r i).val^(if x i then 1 else 0) := by
  refine ⟨realizes_physicalDressing family q _ hq (fun i => reps.actual (r i)),
    dressing_scalar_ne_zero _ (fun i => reps.scalar_ne_zero (r i)),?_⟩
  exact source_dressing_coeff family hfamily q hq reps r

/-- Complete source Lemma7.3: actual four-port dressing, its recorded scalar,
exact image criterion, and odd-order bijectivity. -/
theorem source_cyclic_dressing {m : ℕ} (hm : 3≤m)
    (family : SignatureFamily Scalar) (hfamily : family.Finite)
    (q : Signature Scalar 4) (hq : Gadget.Realizes family .disequality q)
    (reps : CyclicQuaternary.Physical.Representatives family m) :
    (∀r : Roots m,
      Gadget.Realizes family .disequality (physicalDressing q (fun i => reps.matrix (r i))) ∧
      ((2 : Scalar)^4*∏i,reps.scalar (r i))≠0 ∧
      ∀x : Fin 4 → Bool,
        (((2 : Scalar)^4*∏i,reps.scalar (r i))⁻¹ • walsh (physicalDressing q (fun i => reps.matrix (r i)))) x=
          walsh q x*∏i,(r i).val^(if x i then 1 else 0)) ∧
    (∀t : Roots m,(∃r,dressingMap r=t) ↔ SquareTarget t) ∧
    (Odd m → Function.Bijective (@dressingMap m)) :=
  ⟨source_actual_dressing family hfamily q hq reps,
    dressingMap_image_iff (by omega),dressingMap_bijective_odd⟩

end Holant.Projective.CyclicDressing
