import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPurePinsCore
import Holant.Proofs.Hardness.EONegativeSubfamily
import Holant.Proofs.Hardness.GeneralEOClosedCriterion

/-! Canonical whole-current common-sign EO families. Every eligible original
palette label is selected, in every arity, including repeated equal rows. The
selection is a literal label map; it is never a choice of one representative
signature, one quaternary descendant, or separate tractable classes per row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEOSelection
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (sign : EOSign)

abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
def row (i : Fin P.count) : AnySignature AlgebraicComplex := ⟨P.arity i.val,mapped G P i⟩

def Eligible (i : Fin P.count) : Prop :=
  Signature.CentralSupport (mapped G P i) ∧ EONegativeWitness.Supports sign (row G P i)

abbrev Index := {i : Fin P.count // Eligible G P sign i}
local instance : Fintype (Index G P sign) := Fintype.ofFinite _
abbrev count := Fintype.card (Index G P sign)

def index (i : Fin (count G P sign)) : Index G P sign := (Fintype.equivFin _).symm i
def select (k : ℕ) : ℕ := if h : k < count G P sign then (index G P sign ⟨k,h⟩).val.val else 0

theorem select_bound (i : Fin (count G P sign)) : select G P sign i.val < P.count := by
  simp only [select,dif_pos i.isLt]
  exact (index G P sign i).val.isLt

abbrev label := EONegativeSubfamily.label (select G P sign) (select_bound G P sign)
abbrev arity := EONegativeSubfamily.selectedArity (a:=P.arity) (select G P sign)
abbrev table := EONegativeSubfamily.selected (mapped G P) (select G P sign) (select_bound G P sign)
abbrev family := EONegativePairReduction.family (table G P sign)

theorem label_index (i : Fin (count G P sign)) : label G P sign i = (index G P sign i).val := by
  apply Fin.ext
  simp only [label,EONegativeSubfamily.label,select,dif_pos i.isLt]

theorem label_eligible (i : Fin (count G P sign)) : Eligible G P sign (label G P sign i) := by
  rw [label_index]
  exact (index G P sign i).property

theorem label_complete (i : Fin P.count) (h : Eligible G P sign i) :
    ∃j : Fin (count G P sign),label G P sign j=i := by
  refine ⟨Fintype.equivFin _ ⟨i,h⟩,?_⟩
  rw [label_index]
  exact congrArg Subtype.val ((Fintype.equivFin _).symm_apply_apply ⟨i,h⟩)

theorem label_injective : Function.Injective (label G P sign) := by
  intro i j h
  rw [label_index,label_index] at h
  exact (Fintype.equivFin _).symm.injective (Subtype.ext h)

theorem selected_exact (i : Fin (count G P sign)) :
    EONegativePairReduction.signature (table G P sign) i = row G P (label G P sign i) := rfl

theorem central (i : Fin (count G P sign)) : Signature.CentralSupport (table G P sign i) :=
  (label_eligible G P sign i).1

theorem supports (i : Fin (count G P sign)) :
    EONegativeWitness.Supports sign (EONegativePairReduction.signature (table G P sign) i) :=
  (label_eligible G P sign i).2

theorem mapped_nonzero (i : Fin P.count) : mapped G P i ≠ 0 := by
  intro h
  apply P.nonzero i
  funext x
  apply (StableHigherCurrentPurePinsCore.embedding G).injective
  exact (congrFun h x).trans (map_zero _).symm

theorem nonzero (i : Fin (count G P sign)) : table G P sign i≠0 :=
  mapped_nonzero G P (label G P sign i)

theorem preprocessed : Preprocessed (family G P sign) := by
  rintro _ ⟨i,rfl⟩
  exact ⟨P.positive (label G P sign i),nonzero G P sign i⟩

/-- A single class is required across the complete eligible current family. -/
def Compatible : Prop :=
  ∃C : EOClass,∀i : Fin P.count,Eligible G P sign i → EONegativeWitness.Pairings C (row G P i)

theorem compatible_iff : Compatible G P sign ↔ EOTract (preprocess (family G P sign)) := by
  rw [preprocess_eq_self (preprocessed G P sign)]
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨Set.finite_range _,?_,sign,C,?_,?_⟩
    · rintro _ ⟨i,rfl⟩
      exact GeneralEOClosedCriterion.isEO_of_central_nonzero _ (central G P sign i) (nonzero G P sign i)
    · rintro _ ⟨i,rfl⟩
      exact supports G P sign i
    · rintro _ ⟨i,rfl⟩
      exact hC (label G P sign i) (label_eligible G P sign i)
  · rintro ⟨_,_,_,C,_,hC⟩
    refine ⟨C,fun i hi => ?_⟩
    obtain ⟨j,hj⟩ := label_complete G P sign i hi
    have h := hC _ ⟨j,rfl⟩
    rw [selected_exact,hj] at h
    exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEOSelection
end
