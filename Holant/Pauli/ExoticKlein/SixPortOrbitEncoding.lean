import Holant.Pauli.ExoticKlein.SixPortStabilizer
import Holant.Pauli.ExoticKlein.SixPortGeneratorTags

/-! Fast finite tags, proved equivalent to the actual direction actions. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

 def optionDirectionEquiv : Fin 49 ≃ Option Direction where
  toFun i := Fin.cases none (fun j => some (directionEquiv j)) i
  invFun d := match d with | none => 0 | some a => (directionEquiv.symm a).succ
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrArg Fin.succ (directionEquiv.symm_apply_apply j)
  right_inv d := by
    cases d with
    | none => rfl
    | some d => exact congrArg some (directionEquiv.apply_symm_apply d)

 def reverseThree : Equiv.Perm (Fin 3) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

 abbrev TagState := Fin 3 → Fin 49

 def tagStateEquiv : Fin 117649 ≃ TagState :=
  (finFunctionFinEquiv (m := 49) (n := 3)).symm.trans
    (Equiv.arrowCongr reverseThree (Equiv.refl (Fin 49)))

 def stateEquiv : Fin 117649 ≃ DirectionTriple :=
  tagStateEquiv.trans (Equiv.arrowCongr (Equiv.refl (Fin 3)) optionDirectionEquiv)

 def decodeTags (state : TagState) : DirectionTriple := fun j => optionDirectionEquiv (state j)

 theorem stateEquiv_tags (code : Fin 117649) : stateEquiv code = decodeTags (tagStateEquiv code) := rfl

 def tagGenerator (g : Fin 9) (d : Fin 49) : Fin 49 :=
  Fin.ofNat 49 (generatorTags.get (49*g.val+d.val))

/-- Every numeric table entry is checked against the proved physical generator. -/
 theorem tagGenerator_semantics (g : Fin 9) (d : Fin 49) :
    optionDirectionEquiv (tagGenerator g d) = (optionDirectionEquiv d).map (generatorDirection g) := by
  revert g d
  decide +kernel

 def tagGeneratorState (g : Fin 9) (state : TagState) : TagState := fun j => tagGenerator g (state j)

 theorem decodeTags_generator (g : Fin 9) (state : TagState) :
    decodeTags (tagGeneratorState g state) = generatorState g (decodeTags state) := by
  funext j
  exact tagGenerator_semantics g (state j)

 def wordTags : List (Fin 9) → TagState → TagState
  | [],state => state
  | g::rest,state => wordTags rest (tagGeneratorState g state)

 theorem wordTags_semantics (word : List (Fin 9)) (state : TagState) :
    decodeTags (wordTags word state) = wordState word (decodeTags state) := by
  induction word generalizing state with
  | nil => rfl
  | cons g rest ih => rw [wordTags,wordState,ih,decodeTags_generator]

 theorem tagged_word_endpoint (word : List (Fin 9)) (source target : Fin 117649)
    (h : wordTags word (tagStateEquiv source) = tagStateEquiv target) :
    wordState word (stateEquiv source) = stateEquiv target := by
  rw [stateEquiv_tags,stateEquiv_tags,← wordTags_semantics,h]

end
end Holant.Pauli.ExoticKlein.SixPort
