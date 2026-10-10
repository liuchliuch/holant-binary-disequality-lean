import Holant.Proofs.Hardness.GeneralEOPinnedDescentCore
import Holant.Proofs.Hardness.GeneralEONegativeSupportTensor

/-! Central-hole invariants for physical paired-pin descent. These statements
retain actual network denotations and do not identify an abstract pairing
restriction with an available gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleStep
open Holant Holant.Tractable
namespace C
export GeneralEOPinnedDescentCore (network slice10 slice01 supported hole central)
end C
namespace O
export GeneralEOPinnedDescentOperations (word word_weight pinned pinned_denote)
end O
namespace H
export GeneralEONegativeSupportTensor (Triple CentralHole)
end H
variable {K : Type*} [Field K] {n : ℕ}

theorem word_xor (u v r s t z : Bool) (a b c : Fin n → Bool) :
    tripleXor (O.word u v a) (O.word r s b) (O.word t z c) =
      O.word (Bool.xor (Bool.xor u r) t) (Bool.xor (Bool.xor v s) z)
        (tripleXor a b c) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i <;> rfl

theorem complementary_charge (u : Bool) (a : Fin n → Bool) :
    charge (O.word u (!u) a) = charge a := by
  unfold charge
  rw [O.word_weight]
  cases u <;> simp only [Bool.not_false, Bool.not_true, ite_true,
    Bool.false_eq_true, ite_false] <;> omega

@[simp] theorem charge10 (a : Fin n → Bool) : charge (O.word true false a)=charge a :=
  complementary_charge true a

@[simp] theorem charge01 (a : Fin n → Bool) : charge (O.word false true a)=charge a :=
  complementary_charge false a

theorem pinned_central (S : Network K (n+2))
    (he : Signature.CentralSupport S.denote) (u : Bool) :
    Signature.CentralSupport (O.pinned S u).denote := by
  intro x hx
  rw [O.pinned_denote]
  apply he
  rw [O.word_weight]
  cases u <;> simp only [Bool.not_false, Bool.not_true, ite_true,
    Bool.false_eq_true, ite_false] <;> omega

/-- A common oriented prefix can be pinned without losing the support hole. -/
theorem pin_hole (S : Network K (n+2)) (u : Bool) (a b c : Fin n → Bool)
    (ha : S.denote (O.word u (!u) a) ≠ 0)
    (hb : S.denote (O.word u (!u) b) ≠ 0)
    (hc : S.denote (O.word u (!u) c) ≠ 0)
    (hz : S.denote (O.word u (!u) (tripleXor a b c)) = 0)
    (hd : charge (O.word u (!u) (tripleXor a b c)) = 0) :
    H.CentralHole (O.pinned S u).denote := by
  refine ⟨⟨a,b,c,?_,?_,?_⟩,?_,?_⟩
  · simpa only [O.pinned_denote] using ha
  · simpa only [O.pinned_denote] using hb
  · simpa only [O.pinned_denote] using hc
  · exact (O.pinned_denote S u _).trans hz
  · change charge (tripleXor a b c)=0
    simpa only [complementary_charge] using hd

/-- The finite physical cancellation choice preserves a balanced hole when
both complementary extensions of its missing word vanish. -/
theorem descent_hole [CharZero K] (S : Network K (n+2))
    (he : Signature.CentralSupport S.denote) (a b c : Fin n → Bool)
    (ha : C.slice10 S a ≠ 0) (hb : C.slice10 S b ≠ 0)
    (hc : C.slice01 S c ≠ 0)
    (hz10 : C.slice10 S (tripleXor a b c) = 0)
    (hz01 : C.slice01 S (tripleXor a b c) = 0)
    (hd : charge (tripleXor a b c) = 0) :
    H.CentralHole (C.network S he a b c ha hb).denote := by
  have hs := C.supported S he a b c ha hb hc
  exact ⟨⟨a,b,c,hs.1,hs.2.1,hs.2.2⟩,
    C.hole S he a b c ha hb _ hz10 hz01,hd⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOCentralHoleStep
