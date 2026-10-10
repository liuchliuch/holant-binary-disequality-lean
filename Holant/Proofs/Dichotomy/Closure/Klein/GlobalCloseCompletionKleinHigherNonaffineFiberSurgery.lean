import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberCoordinates

/-! Literal edge selection and cross-fusion for tomographic fibers.
All four coefficients are retained, including zeros, and the protected
original edge keeps its original label through the physical surgery. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant.Certificates.MatchingContractionClosure
open MatchingCard MatchingSurgery

namespace Fiber
variable {P J : Type*} [DecidableEq P] [Fintype J] [DecidableEq J]

theorem finite_matching_tensor (ports : (J × Bool) ≃ P) (labels : J → Label) (x : P → Bool) :
    (matching ports).tensor (fun i => labels ((Fintype.equivFin J).symm i)) x =
      ∏ e, E (labels e) (x (ports (e,false))) (x (ports (e,true))) := by
  change (∏ i : Fin (Fintype.card J), E (labels ((Fintype.equivFin J).symm i))
    (x (ports ((Fintype.equivFin J).symm i,false)))
    (x (ports ((Fintype.equivFin J).symm i,true)))) = _
  exact Equiv.prod_comp (Fintype.equivFin J).symm
    (fun e => E (labels e) (x (ports (e,false))) (x (ports (e,true))))

theorem contract_sum (u v : P) (C : Kernel ℂ) (q : Label → Tensor ℂ P) :
    contractPair u v C (fun x => ∑ a, q a x) = fun x => ∑ a, contractPair u v C (q a) x := by
  funext x
  simp only [contractPair,Fintype.sum_bool,Finset.mul_sum,Finset.sum_add_distrib]

variable {r : ℕ}

def deletedMatching (M : Matching P r) (e : Fin r) :
    Matching (Remaining (M.ports (e,false)) (M.ports (e,true))) (Fintype.card (OtherEdges e)) :=
  matching (deletePorts M.ports e)

def deletedLabels (e : Fin r) (labels : Label → Fin r → Label) (a : Label) :
    Fin (Fintype.card (OtherEdges e)) → Label :=
  fun i => labels a ((Fintype.equivFin (OtherEdges e)).symm i).val

def selectedWeight (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e : Fin r) (b a : Label) : ℂ := if labels a e = b then weight a else 0

theorem contract_edge (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e : Fin r) (b : Label) :
    contractPair (M.ports (e,false)) (M.ports (e,true)) (asMatrix (dual b)) (tensor M weight labels) =
      tensor (deletedMatching M e) (selectedWeight weight labels e b) (deletedLabels e labels) := by
  unfold Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.Fiber.tensor
  rw [contract_sum (M.ports (e,false)) (M.ports (e,true)) (asMatrix (dual b))
    (fun a x => weight a*M.tensor (labels a) x)]
  funext x
  apply Finset.sum_congr rfl
  intro a ha
  have he := congrFun (contract_matched M.ports (fun i => asMatrix (E (labels a i))) (weight a) e
    (asMatrix (dual b))) x
  change contractPair _ _ _ (fun z => weight a*M.tensor (labels a) z) x = _ at he
  rw [he,productValue,trace_dual]
  change _ = selectedWeight weight labels e b a*
    (matching (deletePorts M.ports e)).tensor
      (fun i => labels a ((Fintype.equivFin (OtherEdges e)).symm i).val) x
  rw [finite_matching_tensor (deletePorts M.ports e) (fun d : OtherEdges e => labels a d.val) x]
  by_cases h : labels a e = b <;> simp [selectedWeight,h,asMatrix]

def fusedMatching (M : Matching P r) (e f : Fin r) :
    Matching (Remaining (M.ports (e,true)) (M.ports (f,false))) (Fintype.card (OtherEdges f)) :=
  matching (splicePorts M.ports e f)

def fusedLabels (e f : Fin r) (k : Label) (labels : Label → Fin r → Label) (a : Label) :
    Fin (Fintype.card (OtherEdges f)) → Label := fun i =>
  let d := ((Fintype.equivFin (OtherEdges f)).symm i).val
  if d = e then spliceLabel (labels a e) k (labels a f) else labels a d

def fusedWeight (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e f : Fin r) (k a : Label) : ℂ := weight a*spliceScalar (labels a e) k (labels a f)

theorem fusedWeight_zero_iff (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e f : Fin r) (k a : Label) : fusedWeight weight labels e f k a = 0 ↔ weight a = 0 := by
  simp only [fusedWeight,mul_eq_zero,spliceScalar_ne_zero,or_false]

theorem contract_cross_fiber (M : Matching P r) (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (e f : Fin r) (hef : e ≠ f) (k : Label) :
    contractPair (M.ports (e,true)) (M.ports (f,false)) (asMatrix (dual k)) (tensor M weight labels) =
      tensor (fusedMatching M e f) (fusedWeight weight labels e f k) (fusedLabels e f k labels) := by
  unfold Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine.Fiber.tensor
  rw [contract_sum (M.ports (e,true)) (M.ports (f,false)) (asMatrix (dual k))
    (fun a x => weight a*M.tensor (labels a) x)]
  funext x
  apply Finset.sum_congr rfl
  intro a ha
  have he := congrFun (contract_cross M.ports (fun i => asMatrix (E (labels a i))) (weight a) e f hef
    (asMatrix (dual k))) x
  change contractPair _ _ _ (fun z => weight a*M.tensor (labels a) z) x = _ at he
  rw [he,productValue]
  let j : OtherEdges f := ⟨e,hef⟩
  let value : OtherEdges f → ℂ := fun d => E (if d.val = e then spliceLabel (labels a e) k (labels a f) else labels a d.val)
    (x (splicePorts M.ports e f (d,false))) (x (splicePorts M.ports e f (d,true)))
  have hfactor (d : OtherEdges f) :
      spliceFactors (asMatrix (dual k)) (fun i => asMatrix (E (labels a i))) e f d
        (x (splicePorts M.ports e f (d,false))) (x (splicePorts M.ports e f (d,true))) =
      (if d = j then spliceScalar (labels a e) k (labels a f) else 1)*value d := by
    by_cases hd : d = j
    · subst d
      simp only [spliceFactors,j,ite_true,value]
      exact congrFun (congrFun (fuse_dual (labels a e) k (labels a f)) _) _
    · have hd' : d.val ≠ e := fun hh => hd (Subtype.ext hh)
      simp only [spliceFactors,hd',ite_false,hd,one_mul,value,asMatrix,Matrix.of_apply]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ d : OtherEdges f, if d = j then spliceScalar (labels a e) k (labels a f) else 1) =
      spliceScalar (labels a e) k (labels a f) := by simp
  rw [hprod]
  change _ = fusedWeight weight labels e f k a*
    (matching (splicePorts M.ports e f)).tensor
      (fun i => (fun d : OtherEdges f => if d.val = e then spliceLabel (labels a e) k (labels a f)
        else labels a d.val) ((Fintype.equivFin (OtherEdges f)).symm i)) x
  rw [finite_matching_tensor (splicePorts M.ports e f)
    (fun d : OtherEdges f => if d.val = e then spliceLabel (labels a e) k (labels a f) else labels a d.val) x]
  simp only [fusedWeight,mul_assoc,value]

end Fiber
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
