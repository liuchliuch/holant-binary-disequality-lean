import Holant.Proofs.Hardness.GeneralEOCentralHoleStep

/-! The repeated complementary-pattern step of central-hole descent. The
three outcomes use the original network, paired pins, and the proved physical
cancellation repair. No restriction of an arbitrary pairing is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleRepeated
open Holant Holant.Tractable
namespace S
export GeneralEOCentralHoleStep (word_xor complementary_charge charge10 charge01 pinned_central pin_hole descent_hole)
end S
namespace O
export GeneralEOPinnedDescentOperations (word pinned pinned_denote)
end O
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote)
end N
namespace C
export GeneralEOPinnedDescentCore (network slice10 slice01 central)
end C
namespace H
export GeneralEONegativeSupportTensor (CentralHole)
end H
variable {K : Type*} [Field K] {n : ℕ}

def swapPairs : Equiv.Perm (Fin (n+4)) :=
  (Equiv.swap 0 2).trans (Equiv.swap 1 3)

theorem swapPairs_word (u v r s : Bool) (x : Fin n → Bool) :
    (fun i => O.word u v (O.word r s x) (swapPairs i)) =
      O.word r s (O.word u v x) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_
    (fun i => Fin.cases ?_ (fun i => ?_) i) i) i) i
  all_goals simp (disch := omega) [swapPairs, O.word, Equiv.swap_apply_def,
    Fin.ext_iff, Nat.mod_eq_of_lt]
  all_goals rfl

theorem reboundary_central {m : ℕ} (T : Network K m)
    (he : Signature.CentralSupport T.denote) (e : Equiv.Perm (Fin m)) :
    Signature.CentralSupport (N.reboundary T e).denote := by
  intro x hx
  rw [N.reboundary_denote, Tensor.reindex_apply]
  apply he
  have hw : weight (fun i => x (e i))=weight x := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  simpa only [hw] using hx

theorem xor_cancel (a b c : Fin n → Bool) :
    tripleXor a b (tripleXor a b c)=c := by
  funext i
  dsimp [tripleXor]
  cases a i <;> cases b i <;> cases c i <;> rfl

theorem xor_duplicate (a b : Fin n → Bool) : tripleXor a a b=b := by
  funext i
  simp [tripleXor]

def swapped (T : Network K (n+4)) : Network K (n+4) := N.reboundary T swapPairs

theorem swapped_denote (T : Network K (n+4)) (u v r s : Bool) (x : Fin n → Bool) :
    (swapped T).denote (O.word u v (O.word r s x))=
      T.denote (O.word r s (O.word u v x)) := by
  rw [swapped, N.reboundary_denote, Tensor.reindex_apply, swapPairs_word]

def double (u v : Bool) (x : Fin n → Bool) : Fin (n+4) → Bool :=
  O.word u (!u) (O.word v (!v) x)

variable [CharZero K] (T : Network K (n+4))
variable (he : Signature.CentralSupport T.denote) (a b c : Fin n → Bool)
variable (ha : T.denote (double true true a) ≠ 0)
variable (hb : T.denote (double true true b) ≠ 0)

inductive Branch where
  | descent | pinFirst | pinSecond
  deriving DecidableEq, Repr

def select : Branch := by
  classical
  exact if T.denote (double true false (tripleXor a b c))=0 then .descent
    else if T.denote (double true false c)=0 then .pinFirst else .pinSecond

def branchNetwork : Branch → Network K (n+2)
  | .descent => C.network T he (O.word true false a) (O.word true false b)
      (O.word false true c) ha hb
  | .pinFirst => O.pinned T true
  | .pinSecond => O.pinned (swapped T) false

/-- The two extra coefficients select among three actual graph operations. -/
def output : Network K (n+2) := branchNetwork T he a b c ha hb (select T a b c)

omit [CharZero K] in
theorem output_central : Signature.CentralSupport (output T he a b c ha hb).denote := by
  classical
  unfold output select
  split_ifs
  · exact C.central T he _ _ _ ha hb
  · exact S.pinned_central T he true
  · exact S.pinned_central (swapped T) (reboundary_central T he swapPairs) false

variable (hc : T.denote (double false false c) ≠ 0)
variable (hz : T.denote (double false false (tripleXor a b c))=0)
variable (hd : charge (double false false (tripleXor a b c))=0)

include hc hz hd in
theorem output_hole : H.CentralHole (output T he a b c ha hb).denote := by
  classical
  have htail : charge (O.word false true (tripleXor a b c))=0 := by
    simpa only [double, Bool.not_false, S.charge01] using hd
  have hctail : charge (O.word false true c)=0 := by
    have hw : 2*weight (double false false c)=n+4 := by
      by_contra hn
      exact hc (he _ hn)
    have hq : charge (double false false c)=0 := by
      unfold charge
      omega
    simpa only [double, Bool.not_false, S.charge01] using hq
  unfold output select
  split_ifs with hε hζ
  · apply S.descent_hole T he (O.word true false a) (O.word true false b)
      (O.word false true c) ha hb hc
    · simpa [C.slice10, S.word_xor, double] using hε
    · simpa [C.slice01, S.word_xor, double] using hz
    · simpa [S.word_xor] using htail
  · apply S.pin_hole T true (O.word true false a) (O.word true false b)
      (O.word false true (tripleXor a b c)) ha hb hε
    · simpa [S.word_xor, xor_cancel, double] using hζ
    · simpa [S.word_xor, xor_cancel] using hctail
  · apply S.pin_hole (swapped T) false (O.word false true c)
      (O.word true false c) (O.word true false (tripleXor a b c))
    · simpa [swapped_denote, double] using hc
    · simpa [swapped_denote, double] using hζ
    · simpa [swapped_denote, double] using hε
    · simpa [S.word_xor, xor_duplicate, swapped_denote, double] using hz
    · simpa [S.word_xor, xor_duplicate] using htail

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleRepeated
