import Holant.Complexity.BinaryArithmetic.Bits
import Holant.Algebraic.RationalEncoding

/-! Strict scalar specifications using the original bytes.
Mathlib's Nat decoder is total even on high-zero padding. Strict acceptance
therefore explicitly checks its encoder image; no old decoder is redefined. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Scalar
open Computability Holant.Algebraic Holant.Complexity.BinaryArithmetic

namespace NatCodec
/-- The finite machine checks the first bit of the reversed input, or EOF. -/
def good (word : List Bool) : Bool :=
  match word.reverse with
  | [] => true
  | bit :: _ => bit

private theorem canonical_append_bit (word : List Bool) (bit : Bool) :
    Canonical (word++[bit]) ↔ bit=true := by
  induction word with
  | nil => simp [Canonical]
  | cons b rest ih =>
    simpa [Canonical,ih]

theorem good_iff_canonical (word : List Bool) : good word=true ↔ Canonical word := by
  cases hr : word.reverse with
  | nil =>
    have hw : word=[] := by rw [←List.reverse_reverse word,hr]; rfl
    subst word
    simp [good,Canonical]
  | cons bit rest =>
    have hw : word=(bit::rest).reverse := by rw [←hr,List.reverse_reverse]
    have hg : good word=bit := by simp only [good,hr]
    rw [hg,hw,List.reverse_cons,canonical_append_bit]

theorem canonical_word (word : List Bool) (h : Canonical word) :
    word=encodeNat (value word) :=
  canonical_injective word (encodeNat (value word)) h (canonical_encodeNat _)
    (value_encodeNat _).symm

theorem good_iff_encoder_guard (word : List Bool) :
    good word=true ↔ encodingNatBool.encode (decodeNat word)=word := by
  constructor
  · intro h
    have hw := canonical_word word ((good_iff_canonical word).mp h)
    rw [hw,decode_encodeNat]
    rfl
  · intro h
    apply (good_iff_canonical word).mpr
    rw [←h]
    exact canonical_encodeNat _

def decode (word : List Bool) : Option ℕ :=
  if good word then some (decodeNat word) else none

theorem decode_some_iff (word : List Bool) (n : ℕ) :
    decode word=some n ↔ word=encodingNatBool.encode n := by
  constructor
  · intro h
    unfold decode at h
    split at h
    next hg =>
      have hn : decodeNat word=n := Option.some.inj h
      rw [←hn]
      exact ((good_iff_encoder_guard word).mp hg).symm
    next hg => cases h
  · intro h
    rw [h]
    change decode (encodeNat n)=some n
    have hg : good (encodeNat n)=true :=
      (good_iff_canonical _).mpr (canonical_encodeNat n)
    simp only [decode,hg,↓reduceIte,decode_encodeNat]

theorem decode_none_iff (word : List Bool) :
    decode word=none ↔ ¬ ∃ n, word=encodingNatBool.encode n := by
  constructor
  · intro h ⟨n,hn⟩
    have hs := (decode_some_iff word n).mpr hn
    rw [h] at hs
    cases hs
  · intro h
    cases hd : decode word with
    | none => rfl
    | some n => exact False.elim (h ⟨n,(decode_some_iff word n).mp hd⟩)

/-- Same original encoder; the only change is the explicit strict decoder guard. -/
def encoding : Encoding ℕ Bool where
  encode := encodingNatBool.encode
  decode := decode
  decode_encode n := (decode_some_iff _ n).mpr rfl

theorem decode_old_with_guard (word : List Bool) :
    decode word=(encodingNatBool.decode word).bind
      (fun n => if encodingNatBool.encode n=word then some n else none) := by
  change (if good word then some (decodeNat word) else none)=
    (if encodingNatBool.encode (decodeNat word)=word then some (decodeNat word) else none)
  by_cases hg : good word=true
  · have he := (good_iff_encoder_guard word).mp hg
    simp only [if_pos hg,if_pos he]
  · have he : ¬ encodingNatBool.encode (decodeNat word)=word :=
      fun h => hg ((good_iff_encoder_guard word).mpr h)
    simp only [if_neg hg,if_neg he]
end NatCodec

end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Scalar
