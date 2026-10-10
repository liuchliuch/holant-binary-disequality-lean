import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFourier
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineOrthogonalActual

/-! The RM Fourier witness is moved to the literal first pair. An actual
uniform first-pair Gram matrix annihilates both possible masks, so this witness
is incompatible with the real-prime Gram alternative. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFrontFourier
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
open Holant.Dihedral.CompatibleCoefficientLine (pair)
open GlobalCloseCompletionKleinHigherNonaffineFourier
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def frontMask (n : ℕ) (both : Bool) : BinaryVector (n+2) :=
  unitWord 0+(if both then unitWord 1 else 0)

theorem coordinate_unit (e : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    coordinateMap e (unitWord i)=unitWord (e.symm i) := by
  funext j
  simp only [coordinateMap,LinearMap.coe_mk,AddHom.coe_mk,unitWord,Pi.single_apply]
  by_cases he : i=e j
  · have hj : j=e.symm i := by rw [he,e.symm_apply_apply]
    rw [if_pos he.symm,if_pos hj]
  · have hj : j≠e.symm i := by
      intro h
      apply he
      rw [h,e.apply_symm_apply]
    rw [if_neg (Ne.symm he),if_neg hj]

theorem pairWord_front : pairWord n=frontMask n true := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
  · simp [pairWord,prepend,frontMask,unitWord_apply]
  · simp [pairWord,prepend,frontMask,unitWord_apply]
  · have hne : k.succ.succ≠(1:Fin (n+2)) := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_succ,Fin.val_one] at hh
      omega
    simp [pairWord,prepend,frontMask,unitWord_apply,hne]

theorem unit_of_weight_one (v : BinaryVector (n+2)) (weight : binaryWeight v=1) :
    ∃i : Fin (n+2),v=unitWord i := by
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp (show (wordSupport v).card=1 from weight)
  refine ⟨i,?_⟩
  rw [←supportWord_wordSupport v,hi]
  funext j
  simp [supportWord,unitWord_apply]

theorem front_coordinate_reduction (v : BinaryVector (n+2)) (zero : v≠0) (one : v≠ones (n+2)) :
    ∃p : GenerationProgram (n+2),∃both : Bool,p.word v=frontMask n both := by
  obtain ⟨p,small⟩ := coordinate_reduction v zero one
  rcases small with single|double
  · obtain ⟨i,hi⟩ := unit_of_weight_one (p.word v) single
    let e : Equiv.Perm (Fin (n+2)) := Equiv.swap i 0
    refine ⟨GenerationGate.perm e::p,false,?_⟩
    change coordinateMap e.symm (p.word v)=frontMask n false
    rw [hi,coordinate_unit]
    simp [e,frontMask]
  · obtain ⟨e,he⟩ := exists_weightTwo_permutation (p.word v) double
    refine ⟨GenerationGate.perm e::p,true,?_⟩
    change coordinateMap e.symm (p.word v)=frontMask n true
    rw [←he]
    have inverse : coordinateMap e.symm (coordinateMap e (pairWord n))=pairWord n := by
      funext i
      simp [coordinateMap]
    rw [inverse,pairWord_front]

theorem front_fourier_witness (f : BinaryVector (n+2)→ℂ)
    (bad : ¬∀x y : BinaryVector (n+2),dot (ones (n+2)) x=dot (ones (n+2)) y→f x=f y) :
    ∃p : GenerationProgram (n+2),∃both : Bool,
      transform (fun x=>f (p.inverse.word x)) (frontMask n both)≠0 := by
  obtain ⟨v,zero,one,live⟩ := noncentral_witness f bad
  obtain ⟨p,both,he⟩ := front_coordinate_reduction v zero one
  refine ⟨p,both,?_⟩
  rw [←he,transform_action]
  exact live

def words (m : ℕ) : (Fin m→Bool)≃BinaryVector m where
  toFun := vectorWord
  invFun := wordVector
  left_inv := word_vector
  right_inv := vector_word

theorem sum_cons {m : ℕ} (F : (Fin (m+1)→Bool)→ℂ) :
    (∑x,F x)=∑a : Bool,∑z : Fin m→Bool,F (Fin.cons a z) := by
  letI : Fintype (Bool × (Fin m→Bool)) := _root_.instFintypeProd Bool (Fin m→Bool)
  let e : (Bool × (Fin m→Bool))≃(Fin (m+1)→Bool) := Fin.consEquiv (fun _=>Bool)
  have h : (∑ab : Bool × (Fin m→Bool),F (Fin.cons ab.1 ab.2))=∑x,F x := Equiv.sum_comp e F
  rw [Fintype.sum_prod_type] at h
  exact h.symm

theorem sum_pair (F : (Fin (n+2)→Bool)→ℂ) :
    (∑x,F x)=∑a : Bool,∑b : Bool,∑z : Fin n→Bool,F (pair a b z) := by
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_cons]

theorem mask_pair (both a b : Bool) (z : Fin n→Bool) :
    dot (frontMask n both) (vectorWord (pair a b z))=
      boolEquiv a+(if both then boolEquiv b else 0) := by
  cases both <;> simp [frontMask,dot_add_left,dot_unit_left,vectorWord,pair]

theorem gram_front_zero (f : Signature ℂ (n+2)) (d : ℂ)
    (orthogonal : ∀u v : Fin 2→Bool,
      (∑z : Fin n→Bool,f (pair (u 0) (u 1) z)*f (pair (v 0) (v 1) z))=if u=v then d else 0)
    (both : Bool) :
    transform (fun x=>f (wordVector x)^2) (frontMask n both)=0 := by
  have rows (a b : Bool) : (∑z : Fin n→Bool,f (pair a b z)^2)=d := by
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,ite_true,pow_two] using
      orthogonal ![a,b] ![a,b]
  unfold transform
  rw [←Equiv.sum_comp (words (n+2))
    (fun x=>sign (dot (frontMask n both) x)*f (wordVector x)^2)]
  change (∑x : Fin (n+2)→Bool,sign (dot (frontMask n both) (vectorWord x))*f (wordVector (vectorWord x))^2)=0
  simp only [word_vector]
  rw [sum_pair]
  simp_rw [mask_pair,←Finset.mul_sum,rows]
  cases both <;> simp [Fintype.sum_bool,boolEquiv,sign,intSign,show (1+1:ZMod 2)=0 from by decide]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFrontFourier
end
