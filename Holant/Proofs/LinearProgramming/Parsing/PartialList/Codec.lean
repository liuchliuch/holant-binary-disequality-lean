import Holant.Proofs.LinearProgramming.Parsing.Structural.ListMachine
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists

/-! Mathematical transport for an installed allSome-list
controller. allSome and emitted are specifications, never TM2 instructions.
The physical traversal and invalid-word clearing are supplied in Programs.
No new scalar/list wire convention is introduced. -/
open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.PartialList
open Computability Holant.Algebraic Holant.Complexity FixedFieldMachines GraphPreprocessing
open Holant.Complexity.FixedGadgetSubstitution.Compiler

variable {A B : Type} (ea : Encoding A Bool)

def Strict : Prop := ∀ input a, ea.decode input=some a ↔ input=ea.encode a

/-- Proof specification only: every element must return some, in original order. -/
def allSome : List (List Bool) → Option (List A)
  | [] => some []
  | word::words => (ea.decode word).bind
      (fun a => (allSome words).map (fun xs => a::xs))

abbrev wordListEncoding := Structural.WordList.encoding
def decode (input : List Bool) : Option (List A) :=
  (wordListEncoding.decode input).bind (allSome ea)

theorem encoded_words (xs : List A) :
    wordListEncoding.encode (xs.map ea.encode)=(framedListEncoding ea).encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.map_cons,framedListEncoding,framedListEncode,Frame.wordEncoding,
      id_eq] using congrArg (fun tail => true::(frame (ea.encode a)++tail)) ih

theorem allSome_encoded (xs : List A) : allSome ea (xs.map ea.encode)=some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,allSome,Encoding.decode_encode,Option.bind_some,ih,Option.map_some]

theorem allSome_some (hs : Strict ea) (words : List (List Bool)) (xs : List A) :
    allSome ea words=some xs ↔ words=xs.map ea.encode := by
  constructor
  · intro h
    induction words generalizing xs with
    | nil =>
      have hx : ([] : List A)=xs := Option.some.inj h
      subst xs
      rfl
    | cons word words ih =>
      obtain ⟨a,ha,ht⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail,htail,hxs⟩ := Option.map_eq_some_iff.mp ht
      have hhead := (hs word a).mp ha
      have hrest := ih tail htail
      rw [←hxs,hhead,hrest,List.map_cons]
  · intro h
    rw [h]
    exact allSome_encoded ea xs

theorem decode_some_iff (hs : Strict ea) (input : List Bool) (xs : List A) :
    decode ea input=some xs ↔ input=(framedListEncoding ea).encode xs := by
  constructor
  · intro h
    obtain ⟨words,hwords,hxs⟩ := Option.bind_eq_some_iff.mp h
    have hi := (Structural.WordList.decode_some_iff input words).mp hwords
    have hw := (allSome_some ea hs words xs).mp hxs
    rw [hw,encoded_words] at hi
    exact hi
  · intro h
    rw [h,←encoded_words ea xs]
    simp only [decode,Encoding.decode_encode,Option.bind_some,allSome_encoded]

theorem decode_none_iff (hs : Strict ea) (input : List Bool) :
    decode ea input=none ↔ ¬ ∃ xs, input=(framedListEncoding ea).encode xs := by
  constructor
  · intro h ⟨xs,hxs⟩
    have he := (decode_some_iff ea hs input xs).mpr hxs
    rw [h] at he
    cases he
  · intro h
    cases hd : decode ea input with
    | none => rfl
    | some xs => exact False.elim (h ⟨xs,(decode_some_iff ea hs input xs).mp hd⟩)

/-- The old finite-fuel codec retains exactly the same element bytes. -/
theorem old_prefix_some (hs : Strict ea) (fuel : ℕ) (input : List Bool)
    (xs : List A) (suffix : List Bool)
    (h : framedListDecodePrefix ea fuel input=some (xs,suffix)) :
    input=framedListEncode ea xs++suffix := by
  induction fuel generalizing input xs suffix with
  | zero => simp [framedListDecodePrefix] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [framedListDecodePrefix] at h
    | cons bit rest =>
      cases bit with
      | false =>
        have hp : ([],rest)=(xs,suffix) := Option.some.inj h
        have hx : ([] : List A)=xs := congrArg Prod.fst hp
        have ht : rest=suffix := congrArg Prod.snd hp
        rw [←hx,←ht]
        rfl
      | true =>
        obtain ⟨p,hp,hpnext⟩ := Option.bind_eq_some_iff.mp h
        rcases p with ⟨head,remaining⟩
        obtain ⟨a,ha,hanext⟩ := Option.bind_eq_some_iff.mp hpnext
        obtain ⟨tail,htail,hresult⟩ := Option.bind_eq_some_iff.mp hanext
        rcases tail with ⟨tail,suffix'⟩
        have he : (a::tail,suffix')=(xs,suffix) := Option.some.inj hresult
        have hx : a::tail=xs := congrArg Prod.fst he
        have ht : suffix'=suffix := congrArg Prod.snd he
        have hframe := (Frame.unframe_some_iff rest head remaining).mp hp
        have hword := (hs head a).mp ha
        rw [←hx,←ht,hframe,hword,ih remaining tail suffix' htail]
        simp only [framedListEncode,List.cons_append,List.append_assoc]

theorem old_decode_some_iff (hs : Strict ea) (input : List Bool) (xs : List A) :
    (framedListEncoding ea).decode input=some xs ↔ input=(framedListEncoding ea).encode xs := by
  constructor
  · intro h
    obtain ⟨p,hp,hfinal⟩ := Option.bind_eq_some_iff.mp h
    by_cases ht : p.2=[]
    · have hx : p.1=xs := by simpa only [ht,ite_true,Option.some.injEq] using hfinal
      simpa only [framedListEncoding,ht,hx,List.append_nil]
        using old_prefix_some ea hs input.length input p.1 p.2 hp
    · simp only [ht,ite_false] at hfinal
      cases hfinal
  · intro h
    rw [h]
    exact Encoding.decode_encode _ xs

theorem decode_eq_old (hs : Strict ea) (input : List Bool) :
    decode ea input=(framedListEncoding ea).decode input := by
  cases hn : decode ea input with
  | some xs =>
    exact ((old_decode_some_iff ea hs input xs).mpr
      ((decode_some_iff ea hs input xs).mp hn)).symm
  | none =>
    cases ho : (framedListEncoding ea).decode input with
    | none => rfl
    | some xs =>
      have he := (decode_some_iff ea hs input xs).mpr ((old_decode_some_iff ea hs input xs).mp ho)
      rw [hn] at he
      cases he

theorem list_strict (hs : Strict ea) : Strict (framedListEncoding ea) :=
  old_decode_some_iff ea hs

theorem pair_strict (eb : Encoding B Bool) (ha : Strict ea) (hb : Strict eb) :
    Strict (pairEncoding ea eb) := by
  intro input p
  constructor
  · intro h
    obtain ⟨words,hu,hnext⟩ := Option.bind_eq_some_iff.mp h
    rcases words with ⟨left,right⟩
    obtain ⟨a,hea,hnext⟩ := Option.bind_eq_some_iff.mp hnext
    obtain ⟨b,heb,hpair⟩ := Option.bind_eq_some_iff.mp hnext
    have he : (a,b)=p := Option.some.inj hpair
    have hi := (Frame.unframe_some_iff input left right).mp hu
    rw [(ha left a).mp hea,(hb right b).mp heb] at hi
    rw [←he]
    exact hi
  · intro h
    rw [h]
    exact Encoding.decode_encode _ p

/-- Internal failure bytes. This is deliberately NOT an encoded A or packet;
the original structural checker rejects its false marker with trailing true. -/
def chunk (q : Option A) : List Bool :=
  match q with
  | none => [false,true]
  | some a => entry ea a
def emitted (words : List (List Bool)) : List Bool :=
  words.flatMap (fun word => chunk ea (ea.decode word))++[false]

private theorem word_cons_decode (word rest : List Bool) :
    wordListEncoding.decode (true::(frame word++rest))=
      (wordListEncoding.decode rest).map (fun xs => word::xs) := by
  cases hr : wordListEncoding.decode rest with
  | none =>
    apply (Structural.WordList.decode_none_iff _).mpr
    intro h
    have hs := (Structural.WordList.cons_image word rest).mp h
    exact ((Structural.WordList.decode_none_iff rest).mp hr) hs
  | some xs =>
    have hi := (Structural.WordList.decode_some_iff rest xs).mp hr
    rw [hi]
    exact Encoding.decode_encode wordListEncoding (word::xs)

theorem emitted_decode (words : List (List Bool)) :
    wordListEncoding.decode (emitted ea words)=
      (allSome ea words).map (fun xs => xs.map ea.encode) := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    cases hd : ea.decode word with
    | none =>
      simp only [emitted,List.flatMap_cons,hd,chunk,List.cons_append,List.nil_append,
        allSome,Option.bind_none,Option.map_none]
      apply (Structural.WordList.decode_none_iff _).mpr
      intro h
      have impossible := (Structural.WordList.false_image _).mp h
      cases impossible
    | some a =>
      simp only [emitted,List.flatMap_cons,hd,chunk,entry,List.cons_append,List.append_assoc,
        word_cons_decode,allSome,Option.bind_some]
      change (wordListEncoding.decode (emitted ea words)).map (fun xs => ea.encode a::xs)=_
      rw [ih]
      cases allSome ea words <;> rfl

theorem emitted_bytes (words : List (List Bool)) :
    (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding wordListEncoding).encode
      (wordListEncoding.decode (emitted ea words))=
    (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding (framedListEncoding ea)).encode
      (allSome ea words) := by
  rw [emitted_decode]
  cases allSome ea words with
  | none => rfl
  | some xs =>
    change true::wordListEncoding.encode (xs.map ea.encode)=
      true::(framedListEncoding ea).encode xs
    rw [encoded_words]
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.PartialList
