import Holant.Proofs.Hardness.GeneralEOCentralHoleCoordinates
import Holant.Proofs.Hardness.GeneralEOCentralHoleRepeatedLabels

/-! Labelled physical reductions for the two arbitrary-coordinate prefix cases.
All vertices retain their original family labels, including directed 01 pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleCoordinatesLabels
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
set_option backward.isDefEq.respectTransparency false
namespace C
export GeneralEOCentralHoleCoordinates
  (tail2 tail4 prefix_four reboundary_word reboundary_central charge_comp xor_comp
   constant_hole xor_swap_last xor_cycle)
end C
namespace P
export GeneralEOCentralHolePatterns (ConstantColumns RepeatedColumns10 alternating)
end P
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels directed01)
end N
namespace O
export GeneralEOPinnedDescentOperations (pinned)
end O
namespace S
export GeneralEOCentralHoleStep (word_xor pinned_central)
end S
namespace R
export GeneralEOCentralHoleRepeated (double output output_hole output_central)
end R
namespace RL
export GeneralEOCentralHoleRepeatedLabels (labels exact native)
end RL
namespace L
export GeneralEOPinnedDescentLabels (pinnedLabels pinned_exact pinned_native)
end L
namespace LN
export LabelledNetwork (Exact)
end LN
namespace H
export GeneralEONegativeSupportTensor (CentralHole)
end H
variable {K : Type*} [Field K] {n s : ℕ} {arity : ℕ → ℕ}

/-- A smaller actual graph, with exact original labels and native edges. -/
def Smaller (G : (i : Fin s) → Signature K (arity i.val)) (n : ℕ) : Prop :=
  ∃ (m : ℕ), m < n ∧ ∃ (U : Network K m) (UL : Labelling U.shape s 1 arity),
    LN.Exact G U UL ∧ (∀i,U.edge i = Signature.disequality) ∧
    Signature.CentralSupport U.denote ∧ H.CentralHole U.denote

variable (G : (i : Fin s) → Signature K (arity i.val))
variable (T : Network K n) (TL : Labelling T.shape s 1 arity)
variable (j : Fin s) (hj : (⟨arity j.val,G j⟩ : AnySignature K) = ⟨2,N.directed01⟩)
variable (hL : LN.Exact G T TL) (hn : ∀i,T.edge i = Signature.disequality)
variable (he : Signature.CentralSupport T.denote) (a b c : Fin n → Bool)
variable (ha : T.denote a ≠ 0) (hb : T.denote b ≠ 0) (hc : T.denote c ≠ 0)
variable (hz : T.denote (tripleXor a b c) = 0) (hd : charge (tripleXor a b c) = 0)

include hj hL hn he ha hb hc hz hd

/-- The common complementary prefix removes two genuine boundary ports. -/
theorem constant_reduce (h : 2 ≤ n) (e : Equiv.Perm (Fin n))
    (hp : P.ConstantColumns a b c (fun i => e (Fin.castLE h i))) : Smaller G n := by
  obtain ⟨m,rfl⟩ : ∃m,n=m+2 := ⟨n-2,by omega⟩
  let U := N.reboundary T e.symm
  let UL := N.reboundaryLabels T TL e.symm
  refine ⟨m,by omega,O.pinned U false,L.pinnedLabels G U UL j hj false,?_,?_,?_,?_⟩
  · exact L.pinned_exact G U UL j hj hL false
  · exact L.pinned_native U hn false
  · exact S.pinned_central U (C.reboundary_central T e he) false
  · exact C.constant_hole T a b c ha hb hc hz hd h e hp

variable [CharZero K]

/-- Ordered repeated columns normalize to the proved physical cancellation step. -/
theorem repeated_ordered_reduce (h : 4 ≤ n) (e : Equiv.Perm (Fin n))
    (pa : a ∘ (fun i => e (Fin.castLE h i)) = P.alternating true)
    (pb : b ∘ (fun i => e (Fin.castLE h i)) = P.alternating true)
    (pc : c ∘ (fun i => e (Fin.castLE h i)) = P.alternating false) : Smaller G n := by
  obtain ⟨m,rfl⟩ : ∃m,n=m+4 := ⟨n-4,by omega⟩
  let U := N.reboundary T e.symm
  let UL := N.reboundaryLabels T TL e.symm
  let aa := C.tail4 (a ∘ e)
  let bb := C.tail4 (b ∘ e)
  let cc := C.tail4 (c ∘ e)
  have ea : a ∘ e = R.double true true aa := C.prefix_four (a ∘ e) true h pa
  have eb : b ∘ e = R.double true true bb := C.prefix_four (b ∘ e) true h pb
  have ec : c ∘ e = R.double false false cc := C.prefix_four (c ∘ e) false h pc
  have hx : (tripleXor a b c) ∘ e = R.double false false (tripleXor aa bb cc) := by
    rw [←C.xor_comp,ea,eb,ec]
    simp only [R.double,S.word_xor,Bool.not_true,Bool.not_false,Bool.xor_self,
      Bool.false_xor]
  have ua : U.denote (R.double true true aa) ≠ 0 := by
    simpa only [U,←ea,C.reboundary_word] using ha
  have ub : U.denote (R.double true true bb) ≠ 0 := by
    simpa only [U,←eb,C.reboundary_word] using hb
  have uc : U.denote (R.double false false cc) ≠ 0 := by
    simpa only [U,←ec,C.reboundary_word] using hc
  have uz : U.denote (R.double false false (tripleXor aa bb cc)) = 0 := by
    simpa only [U,←hx,C.reboundary_word] using hz
  have ud : charge (R.double false false (tripleXor aa bb cc)) = 0 := by
    simpa only [←hx,C.charge_comp] using hd
  have ue : Signature.CentralSupport U.denote := C.reboundary_central T e he
  refine ⟨m+2,by omega,R.output U ue aa bb cc ua ub,
    RL.labels G U UL j hj ue aa bb cc ua ub,?_,?_,?_,?_⟩
  · exact RL.exact G U UL j hj ue aa bb cc ua ub hL
  · exact RL.native U ue aa bb cc ua ub hn
  · exact R.output_central U ue aa bb cc ua ub
  · exact R.output_hole U ue aa bb cc ua ub uc uz ud

/-- All three possible exceptional support rows give a labelled smaller graph. -/
theorem repeated_reduce (h : 4 ≤ n) (e : Equiv.Perm (Fin n))
    (hp : P.RepeatedColumns10 a b c (fun i => e (Fin.castLE h i))) : Smaller G n := by
  rcases hp with hp | hp | hp
  · exact repeated_ordered_reduce G T TL j hj hL hn he a b c ha hb hc hz hd h e
      hp.1 hp.2.1 hp.2.2
  · apply repeated_ordered_reduce G T TL j hj hL hn he a c b ha hc hb
      (by simpa only [C.xor_swap_last] using hz)
      (by simpa only [C.xor_swap_last] using hd) h e hp.1 hp.2.1 hp.2.2
  · apply repeated_ordered_reduce G T TL j hj hL hn he b c a hb hc ha
      (by simpa only [C.xor_cycle] using hz)
      (by simpa only [C.xor_cycle] using hd) h e hp.1 hp.2.1 hp.2.2

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleCoordinatesLabels
