import Holant.Proofs.Hardness.ComplexNonselfdualCompression
import Holant.Proofs.Hardness.FiveSupportEOOrdering
import Holant.Proofs.Hardness.GeneralGeometricCapLocal

/-! Literal one-, two- and four-original-vertex networks for every complex
exactly-five-supported EO tensor. A cancelled fourth-stage coefficient gives
an unequal-norm cap on the actual two-copy output. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportLocal
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export ComplexNonselfdualCompression (compressed compressed_eo compressed_entries compressNetwork compressNetwork_denote)
end C
namespace O
export FiveSupportEOOrdering (ExactlyFive orderAt missingIndex oriented oriented_eo oriented_b_zero
  middleCoeff reindex_middleCoeff middleIndexAt_ne missing_unique)
end O
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

def oriented (M : Signature K 4) (i : Fin 6) := Tensor.reindex (O.orderAt i) M
def first (M : Signature K 4) (i : Fin 6) := C.compressed (oriented M i)

/-- This swaps b/y and d/w, and fixes c/z. -/
def flip : Equiv.Perm (Fin 4) := O.orderAt 5

def last (M : Signature K 4) (i : Fin 6) : Signature K 4 :=
  let e := entries (first M i)
  table ⟨0,e.d*(e.b+e.y),e.c^2,e.b^2+e.d^2,e.d^2+e.y^2,e.c^2,e.d*(e.b+e.y),0⟩

def network (M : Signature K 4) (i : Fin 6) (k : Fin 3) : Network K 4 :=
  let one := R.reindex (Network.corolla M) (O.orderAt i)
  let two := C.compressNetwork one
  ![one,two,ExactTwoChain.series two (R.reindex two flip)] k

def output (M : Signature K 4) (i : Fin 6) (k : Fin 3) : Signature K 4 :=
  ![oriented M i,first M i,last M i] k

theorem oriented_eo (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) :
    DenseEOUnitLocal.EOSupport (oriented M i) := by
  intro x hx
  apply he
  have hw : weight (fun j=>x (O.orderAt i j))=weight x :=
    Equiv.sum_comp (O.orderAt i) (fun j=>if x j then 1 else 0)
  simpa only [hw] using hx

theorem first_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) :
    (network M i 1).denote=first M i := by
  apply C.compressNetwork_denote
  · rw [R.reindex_denote,Network.denote_corolla]; rfl
  · exact oriented_eo M he i

theorem last_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) :
    (network M i 2).denote=last M i := by
  funext x
  change (ExactTwoChain.series (network M i 1) (R.reindex (network M i 1) flip)).denote x=_
  rw [ExactTwoChain.series_denote]
  simp only [R.reindex_denote,first_denote M he i,Tensor.reindex_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [last,first,C.compressed,table,entries,flip,O.orderAt,h0,h1,h2,h3]
  all_goals ring

theorem denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) (k : Fin 3) :
    (network M i k).denote=output M i k := by
  fin_cases k
  · simp [network,output,oriented,R.reindex_denote,Network.denote_corolla]
  · exact first_denote M he i
  · exact last_denote M he i

theorem last_eo (M : Signature K 4) (i : Fin 6) : DenseEOUnitLocal.EOSupport (last M i) := by
  intro x hx
  rw [Holant.EightVertex.ProductAnchor.weight_four] at hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals try norm_num [h0,h1,h2,h3] at hx
  all_goals simp [last,table,h0,h1,h2,h3]

theorem output_eo (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) (k : Fin 3) :
    DenseEOUnitLocal.EOSupport (output M i k) := by
  fin_cases k
  · exact oriented_eo M he i
  · exact C.compressed_eo _
  · exact last_eo M i

def alpha (M : Signature K 4) := (entries (O.oriented M)).c*(entries (O.oriented M)).z
def beta (M : Signature K 4) := (entries (O.oriented M)).d*(entries (O.oriented M)).w
def gamma (M : Signature K 4) := 2*(entries (O.oriented M)).w*(entries (O.oriented M)).y

theorem selected_entries (M : Signature K 4) (hm : O.ExactlyFive M) :
    entries (first M (O.missingIndex M))=⟨0,0,alpha M,beta M,beta M,alpha M,gamma M,0⟩ := by
  have hb := O.oriented_b_zero M hm
  change entries (C.compressed (O.oriented M))=_
  rw [C.compressed_entries,hb]
  simp only [zero_mul,mul_zero,zero_add,alpha,beta,gamma]

theorem selected_nonzero [CharZero K] (M : Signature K 4) (hm : O.ExactlyFive M) :
    alpha M≠0 ∧ beta M≠0 ∧ gamma M≠0 := by
  have hn (j : Fin 6) (hj : j≠0) : O.middleCoeff (O.oriented M) j≠0 := by
    change O.middleCoeff (Tensor.reindex (O.orderAt (O.missingIndex M)) M) j≠0
    rw [O.reindex_middleCoeff]
    exact (O.missing_unique M hm).2 _ (O.middleIndexAt_ne _ _ hj)
  exact ⟨mul_ne_zero (hn 1 (by decide)) (hn 4 (by decide)),
    mul_ne_zero (hn 2 (by decide)) (hn 3 (by decide)),
    mul_ne_zero (mul_ne_zero (by norm_num) (hn 3 (by decide))) (hn 5 (by decide))⟩

theorem selected_last_entries (M : Signature K 4) (hm : O.ExactlyFive M) :
    entries (last M (O.missingIndex M))=
      ⟨0,beta M*gamma M,alpha M^2,beta M^2,beta M^2+gamma M^2,alpha M^2,beta M*gamma M,0⟩ := by
  change (⟨0,(entries (first M (O.missingIndex M))).d*((entries (first M (O.missingIndex M))).b+(entries (first M (O.missingIndex M))).y),
    (entries (first M (O.missingIndex M))).c^2,
    (entries (first M (O.missingIndex M))).b^2+(entries (first M (O.missingIndex M))).d^2,
    (entries (first M (O.missingIndex M))).d^2+(entries (first M (O.missingIndex M))).y^2,
    (entries (first M (O.missingIndex M))).c^2,
    (entries (first M (O.missingIndex M))).d*((entries (first M (O.missingIndex M))).b+(entries (first M (O.missingIndex M))).y),0⟩ : Entries K)=_
  rw [selected_entries M hm]
  simp

theorem selected_last_middle [CharZero K] (M : Signature K 4) (hm : O.ExactlyFive M)
    (hq : beta M^2+gamma M^2≠0) : DenseEOUnitLocal.NonzeroMiddle (last M (O.missingIndex M)) := by
  have hn := selected_nonzero M hm
  unfold DenseEOUnitLocal.NonzeroMiddle
  rw [selected_last_entries M hm]
  exact ⟨mul_ne_zero hn.2.1 hn.2.2,pow_ne_zero 2 hn.1,pow_ne_zero 2 hn.2.1,hq,
    pow_ne_zero 2 hn.1,mul_ne_zero hn.2.1 hn.2.2⟩

theorem selected_first_middle [CharZero K] (M : Signature K 4) (hm : O.ExactlyFive M) :
    AdaptiveEOUnitLocal.NonzeroMiddle (first M (O.missingIndex M)) := by
  have hn := selected_nonzero M hm
  unfold AdaptiveEOUnitLocal.NonzeroMiddle PartialEOUnitLocal.RequiredEntries
  rw [selected_entries M hm]
  exact ⟨hn.1,hn.2.1,hn.1,hn.2.2⟩

theorem cancellation_roots (D Y : ℂ) (h : D^2+Y^2=0) : Y=Complex.I*D ∨ Y=-(Complex.I*D) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [mul_pow,Complex.I_sq]
  linear_combination h

theorem cancellation_normSq (D Y : ℂ) (h : D^2+Y^2=0) :
    Complex.normSq (D+Y)=2*Complex.normSq D := by
  rcases cancellation_roots D Y h with rfl | rfl
  all_goals simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]; ring

theorem cancellation_cap (M : Signature ℂ 4) (hm : O.ExactlyFive M)
    (hq : beta M^2+gamma M^2=0) :
    GeneralGeometricCapLocal.Applicable (first M (O.missingIndex M)) := by
  have hn := selected_nonzero M hm
  have hs := cancellation_normSq (beta M) (gamma M) hq
  have hp : 0<Complex.normSq (beta M) := Complex.normSq_pos.mpr hn.2.1
  have hnz : beta M+gamma M≠0 := by
    intro hz
    rw [hz] at hs
    simp only [map_zero] at hs
    linarith
  have hne : ‖beta M‖≠‖beta M+gamma M‖ := by
    intro hh
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,←hh] at hs
    rw [Complex.normSq_eq_norm_sq] at hp
    linarith
  refine ⟨(1,false),?_,?_,?_⟩
  all_goals simp only [GeneralCancellationCapPin.oriented,GeneralCancellationCapPin.coefficients,
    Bool.false_eq_true,↓reduceIte,selected_entries M hm,Matrix.cons_val_one,Matrix.cons_val_zero,
    zero_add]
  · exact hn.2.1
  · exact hnz
  · exact hne

def labels (M : Signature K 4) (i : Fin 6) (k : Fin 3) :
    Labelling (network M i k).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases k <;> fin_cases v <;> rfl
  edge _ := 0

abbrev template (M : Signature K 4) (i : Fin 6) (k : Fin 3) := (labels M i k).template
theorem valid (M : Signature K 4) (i : Fin 6) (k : Fin 3) :
    (template M i k).WellFormed 1 1 (fun _=>4) := (labels M i k).wellFormed
theorem counts (M : Signature K 4) (i : Fin 6) (k : Fin 3) :
    (template M i k).vertices.length=![1,2,4] k ∧
      (template M i k).edges.length=![0,2,6] k := by
  fin_cases k <;> exact ⟨rfl,rfl⟩
theorem template_denote (M : Signature K 4) (he : DenseEOUnitLocal.EOSupport M) (i : Fin 6) (k : Fin 3) :
    ((template M i k).network (valid M i k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=output M i k := by
  rw [←denote M he i k]
  apply Labelling.denote_template_of_labels (labels M i k) _ _ (network M i k).vertex (network M i k).edge
  · intro v x; fin_cases k <;> fin_cases v <;> rfl
  · intro e x y; fin_cases k <;> fin_cases e <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportLocal
