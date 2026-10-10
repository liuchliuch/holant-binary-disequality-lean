import Holant.Proofs.Hardness.GeneralEOCommonSignPairing
import Holant.Proofs.Hardness.GeneralEOClosedCriterion

/-! A failed common-sign criterion selects two ordered restrictions. Their
original labels may coincide while the selected pairings remain independent.
Both actual full-arity restrictions are nonzero and have closed support. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCommonSignSelection
open Holant Holant.Tractable
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible restrict)
end L
namespace R
export EONegativePairReduction (family signature Kept)
end R
namespace S
export EONegativeSubfamily (selectedArity selected)
end S
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (sign : EOSign) (he : ∀i,Signature.CentralSupport (G i))
variable (hs : ∀i,EONegativeWitness.Supports sign (R.signature G i))
variable (negative : ¬EOTract (preprocess (R.family G)))

include he hs negative in
theorem class_failure (C : EOClass) : ∃ i : Fin s, R.Kept G i ∧
    ∃ p : OrientedPerfectPairing (a i.val), ¬C.Holds (p.restrict (G i)) := by
  classical
  by_contra h
  push Not at h
  apply negative
  refine ⟨(Set.finite_range (R.signature G)).subset (fun _ hg => hg.1),?_,sign,C,?_,?_⟩
  · rintro g ⟨⟨i,rfl⟩,hi⟩
    exact GeneralEOClosedCriterion.isEO_of_central_nonzero (G i) (he i) hi.2
  · rintro g ⟨⟨i,rfl⟩,_⟩
    exact hs i
  · rintro g ⟨⟨i,rfl⟩,hi⟩ p
    exact h i hi p

structure Choice where
  first : Fin s
  second : Fin s
  first_kept : R.Kept G first
  second_kept : R.Kept G second
  first_pairing : OrientedPerfectPairing (a first.val)
  second_pairing : OrientedPerfectPairing (a second.val)
  first_failure : ¬Affine (first_pairing.restrict (G first))
  second_failure : ¬Product (second_pairing.restrict (G second))

include he hs negative in
theorem choice_exists : Nonempty (Choice G) := by
  obtain ⟨i,hi,p,hp⟩ := class_failure G sign he hs negative .affine
  obtain ⟨j,hj,q,hq⟩ := class_failure G sign he hs negative .product
  exact ⟨⟨i,j,hi,hj,p,q,hp,hq⟩⟩

def choose : Choice G := Classical.choice (choice_exists G sign he hs negative)

variable (c : Choice G)
def indices (k : ℕ) : ℕ := if k=0 then c.first.val else c.second.val
abbrev arity := S.selectedArity (a:=a) (indices G c)
theorem bounded (i : Fin 2) : indices G c i.val<s := by
  unfold indices
  split <;> first | exact c.first.isLt | exact c.second.isLt

def originals := S.selected G (indices G c) (bounded G c)
def pairings (i : Fin 2) : OrientedPerfectPairing (arity G c i.val) := by
  refine Fin.cases c.first_pairing (fun j => ?_) i
  exact Fin.cases c.second_pairing (fun k => Fin.elim0 k) j

def family (i : Fin 2) : Signature AlgebraicComplex (arity G c i.val) :=
  L.restrict (pairings G c i) (originals G c i)

theorem compressed_restrict {n : ℕ} (p : OrientedPerfectPairing n)
    (f : Signature AlgebraicComplex n) : p.restrict (L.restrict p f)=p.restrict f := by
  funext z
  change (if L.Compatible p (p.word z) then f (p.word z) else 0)=f (p.word z)
  apply ite_eq_left
  intro j
  simp [OrientedPerfectPairing.word]

theorem restriction_nonzero {n : ℕ} (p : OrientedPerfectPairing n)
    (f : Signature AlgebraicComplex n) (C : EOClass) (hf : ¬C.Holds (p.restrict f)) :
    L.restrict p f≠0 := by
  intro hz
  have hc : p.restrict f=0 := by
    rw [←compressed_restrict p f,hz]
    rfl
  apply hf
  rw [hc]
  cases C <;> simp [EOClass.Holds]

theorem nonzero (i : Fin 2) : family G c i≠0 := by
  fin_cases i
  · exact restriction_nonzero c.first_pairing (G c.first) .affine c.first_failure
  · exact restriction_nonzero c.second_pairing (G c.second) .product c.second_failure

include he in
theorem central (i : Fin 2) : Signature.CentralSupport (family G c i) := by
  intro x hx
  change (if L.Compatible (pairings G c i) x then originals G c i x else 0)=0
  split_ifs
  · fin_cases i
    · exact he c.first x hx
    · exact he c.second x hx
  · rfl

include hs in
theorem closed (i : Fin 2) : GeneralEONegativeClosedSupport.Closed (family G c i) := by
  apply GeneralEOCommonSignPairing.restricted_closed (pairings G c i) (originals G c i) sign
  fin_cases i
  · exact hs c.first
  · exact hs c.second

theorem pairing_failures :
    (¬EONegativeWitness.Pairings .affine ⟨arity G c 0,family G c 0⟩) ∧
    (¬EONegativeWitness.Pairings .product ⟨arity G c 1,family G c 1⟩) := by
  constructor
  · intro h
    have hh := h (pairings G c 0)
    rw [family,compressed_restrict] at hh
    exact c.first_failure hh
  · intro h
    have hh := h (pairings G c 1)
    rw [family,compressed_restrict] at hh
    exact c.second_failure hh

include he hs in
theorem compressed_failures :
    (¬∀i,Affine (GeneralEOPairedFamilyExtractionChoice.compressed (family G c)
      (central G he c) (nonzero G c) (closed G sign hs c) i)) ∧
    (¬∀i,Product (GeneralEOPairedFamilyExtractionChoice.compressed (family G c)
      (central G he c) (nonzero G c) (closed G sign hs c) i)) := by
  constructor
  · intro h
    exact (pairing_failures G c).1 ((GeneralEOPairedCSPFamilyFieldClosed.class_iff
      (family G c) (central G he c) (nonzero G c) (closed G sign hs c) 0 .affine).mp (h 0))
  · intro h
    exact (pairing_failures G c).2 ((GeneralEOPairedCSPFamilyFieldClosed.class_iff
      (family G c) (central G he c) (nonzero G c) (closed G sign hs c) 1 .product).mp (h 1))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCommonSignSelection
