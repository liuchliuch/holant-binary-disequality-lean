import Holant.Pauli.ExoticKlein.SixPortPermutationSymmetry

/-! Nine proved physical stabilizer generators and semantic transport along
finite words. No group-order, orbit-count, or classification table is assumed. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def generatorDirection (g : Fin 9) : Equiv.Perm Direction :=
  if h : g.val < 6 then pairedDirection ⟨g.val,h⟩
  else permutationDirection ⟨g.val-6,by omega⟩

 def generatorAction (g : Fin 9) : ResidualAction :=
  if h : g.val < 6 then pairedAction ⟨g.val,h⟩
  else permutationAction ⟨g.val-6,by omega⟩

 theorem generatorAction_direction (g : Fin 9) : (generatorAction g).direction = generatorDirection g := by
  unfold generatorAction generatorDirection
  split_ifs <;> rfl

 theorem generator_fixes_base (g : Fin 9) : generatorDirection g baseDirection = baseDirection := by
  unfold generatorDirection
  split_ifs
  · exact pairedDirection_fixes_base _
  · exact permutationDirection_fixes_base _

 theorem generator_involutive (g : Fin 9) : Function.Involutive (generatorDirection g) := by
  unfold generatorDirection
  split_ifs
  · exact pairedDirection_involutive _
  · exact permutedDirection_involutive _

 def generatorState (g : Fin 9) (state : DirectionTriple) : DirectionTriple :=
  fun j => (state j).map (generatorDirection g)

 theorem generatorState_involutive (g : Fin 9) : Function.Involutive (generatorState g) := by
  intro state
  funext j
  cases h : state j with
  | none => simp [generatorState,h]
  | some d =>
    simp only [generatorState,h,Option.map_some]
    exact congrArg some (generator_involutive g d)

 theorem generator_solved_back (g : Fin 9) (state : DirectionTriple) (hs : Solved (generatorState g state)) :
    Solved state := by
  have hf : (generatorAction g).direction baseDirection = baseDirection := by
    rw [generatorAction_direction,generator_fixes_base]
  have hm : (generatorAction g).mapState state = generatorState g state := by
    funext j
    simp only [ResidualAction.mapState,generatorState,generatorAction_direction]
  apply (generatorAction g).solved_back hf state
  rwa [hm]

 theorem generator_solved_iff (g : Fin 9) (state : DirectionTriple) : Solved (generatorState g state) ↔ Solved state := by
  constructor
  · exact generator_solved_back g state
  · intro hs
    apply generator_solved_back g (generatorState g state)
    rwa [generatorState_involutive]

 def wordState : List (Fin 9) → DirectionTriple → DirectionTriple
  | [],state => state
  | g::rest,state => wordState rest (generatorState g state)

 theorem wordState_solved_iff (word : List (Fin 9)) (state : DirectionTriple) :
    Solved (wordState word state) ↔ Solved state := by
  induction word generalizing state with
  | nil => rfl
  | cons g rest ih =>
    rw [wordState,ih,generator_solved_iff]

/-- Certified physical words may reduce exhaustive coverage to representative
triples; the actual representatives and words still require finite validation. -/
 theorem solved_of_word_representative (state representative : DirectionTriple) (word : List (Fin 9))
    (hw : wordState word state = representative) (hs : Solved representative) : Solved state := by
  apply (wordState_solved_iff word state).mp
  rwa [hw]

end
end Holant.Pauli.ExoticKlein.SixPort
